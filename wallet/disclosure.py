#!/usr/bin/env python3
"""Disclosure receipts: show which notes a spend consumed and created, without
giving away the spending key.

A note's nullifier is Poseidon3(4, K, Poseidon2(cm, index)) with the nullifier
key K = Poseidon2(D, spend_key). Given K and the note's position, anyone can
recompute the nullifier and find the spend that published it, and the spend
proof ties that nullifier to exactly this note. K cannot spend: a proof needs
spend_key itself. Following notes from spend to spend traces funds from a
public deposit to a withdrawal. A receipt proves these links and amounts, not
who presents it or where the funds came from before the deposit.

  disclosure.py export --rpc URL --config CONFIG --fixture FIXTURE [--only CM,...] --output PATH
  disclosure.py verify --rpc URL --config CONFIG --receipt PATH
"""
import argparse
import json
import sys
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "reference"))
import wallet as w  # noqa: E402
from eth_hash.auto import keccak  # noqa: E402
from poseidon_bn254 import TAG_LEAF, hex32, p2, tagged  # noqa: E402

RECEIPT, VERSION = "minimal-shielded-pool/disclosure", 1
SPEND_FIELDS = ("root", "rootSlot", "epoch", "domain", "nf1", "nf2", "outCm1", "outCm2",
                "publicAmount", "fee", "recipient", "authorizer")
SETTLE_SELECTOR = keccak(b"settle((bytes32,uint64,uint64,bytes32,bytes32,bytes32,bytes32,bytes32,"
                         b"uint256,uint256,address,address))")[:4]
LEAF_APPENDED = "0x" + keccak(b"LeafAppended(bytes32,uint64,uint32,bytes32)").hex()
NOTE_SPENT = "0x" + keccak(b"NoteSpent(bytes32)").hex()


class ReceiptError(Exception):
    """The receipt does not hold against the chain, or the chain could not be read."""


def nullifier(key, cm, index):
    return tagged(w.TAG_OCCURRENCE_NULL, key, p2(cm, index))


class RpcChain:
    def __init__(self, url):
        self.url = url

    def call(self, method, params):
        request = urllib.request.Request(
            self.url, headers={"content-type": "application/json"},
            data=json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode())
        try:
            reply = json.loads(urllib.request.urlopen(request, timeout=30).read())
        except (OSError, ValueError) as error:
            raise ReceiptError(f"{method} request failed: {error}") from None
        if "error" in reply:
            raise ReceiptError(f"{method} failed: {reply['error']}")
        return reply["result"]

    def chain_id(self):
        return int(self.call("eth_chainId", []), 16)

    def transaction(self, tx_hash):
        tx = self.call("eth_getTransactionByHash", [tx_hash])
        receipt = self.call("eth_getTransactionReceipt", [tx_hash])
        if not tx or not receipt:
            raise ReceiptError(f"transaction {tx_hash} is not on this chain")
        try:
            frames = [{"mode": int(f["mode"], 16), "to": int(f["to"], 16),
                       "data": bytes.fromhex(f["data"][2:]), "status": int(r["status"], 16),
                       "logs": r["logs"]}
                      for f, r in zip(tx.get("frames") or [], receipt.get("frameReceipts") or [])]
            return {"hash": tx_hash, "sender": int(tx.get("sender") or tx["from"], 16),
                    "frames": frames, "logs": receipt["logs"]}
        except (KeyError, TypeError, ValueError) as error:
            raise ReceiptError(f"unexpected RPC response for {tx_hash}: {error!r}") from None

    def logs(self, address, topics, from_block=0):
        found = self.call("eth_getLogs", [{"address": f"0x{address:040x}", "topics": topics,
                                           "fromBlock": hex(from_block), "toBlock": "latest"}])
        return [{"tx": l["transactionHash"].lower(), "address": l["address"], "topics": l["topics"],
                 "data": l["data"]} for l in found]


def _is(log, address, first_topic):
    return int(log["address"], 16) == address and log["topics"][:1] == [first_topic]


def appended(log):
    """(cm, epoch, index) of a LeafAppended log."""
    return int(log["topics"][1], 16), int(log["topics"][2], 16), int(log["data"][2:66], 16)


def export(chain, chain_id, pool, fixture, only=None, from_block=0):
    """A receipt for the notes a generator fixture opens. It reads the pool's
    LeafAppended and NoteSpent logs once and matches them locally, so the RPC
    does not learn which notes are disclosed. spend_key and rho stay out."""
    leaves, spent_in = {}, {}
    for log in chain.logs(pool, [[LEAF_APPENDED, NOTE_SPENT]], from_block):
        if log["topics"][0] == LEAF_APPENDED:
            cm, epoch, index = appended(log)
            leaves.setdefault(cm, []).append((epoch, index, log["tx"]))
        else:
            spent_in[int(log["topics"][1], 16)] = log["tx"]
    notes = {}
    for entry in fixture.values():
        if not isinstance(entry, dict) or "inputs" not in entry:
            continue
        # Inputs name their leaf, a dummy's nullifier uses leaf 0, and outputs
        # are found by commitment. One note can appear as an output and an input.
        mentions = [(i, int(entry["epoch"]), i["leaf"] if i["leaf"] is not None else 0) for i in entry["inputs"]]
        mentions += [(o, None, None) for o in entry.get("output_openings", [])]
        for m, epoch, index in mentions:
            sk, rho, value = int(m["spend_key"], 16), int(m["rho"], 16), int(m["value"])
            note = notes.setdefault(w.commitment(sk, rho, value),
                                    {"sk": sk, "inner": w.inner(sk, rho), "value": value, "places": set()})
            if index is not None:
                note["places"].add((epoch, index))
    out = []
    for cm, n in sorted(notes.items(), key=lambda item: (item[1]["value"] == 0, item[0])):
        if only and not any(hex32(cm).startswith(prefix.lower()) for prefix in only):
            continue
        if n["value"] == 0:  # a dummy input is never in the tree; only its spend shows
            places = [(epoch, index, None) for epoch, index in n["places"]]
        else:
            places = [(e, i, h) for e, i, h in leaves.get(cm, []) if not n["places"] or (e, i) in n["places"]]
        for epoch, index, created in places:
            key = p2(w.domain_scalar(chain_id, pool, epoch), n["sk"])
            spent = spent_in.get(nullifier(key, cm, index))
            if n["value"] == 0 and spent is None:
                continue
            note = {"epoch": epoch, "index": index, "cm": hex32(cm), "inner": hex32(n["inner"]),
                    "value": str(n["value"])}
            note.update({"dummy": True} if n["value"] == 0 else {"created": created})
            if spent is not None:
                note.update({"spent": spent, "nullifierKey": hex32(key)})
            out.append(note)
    return {"receipt": RECEIPT, "version": VERSION, "chainId": chain_id,
            "pool": f"0x{pool:040x}", "notes": out}


def decode_spend(tx, pool):
    """The settlement fields and inserted outputs of a pool spend."""
    if tx["sender"] != pool:
        raise ReceiptError(f"{tx['hash']} is not a spend of this pool")
    frames = [f for f in tx["frames"] if f["mode"] == 2 and f["to"] == pool and f["data"][:4] == SETTLE_SELECTOR]
    if len(frames) != 1 or len(frames[0]["data"]) != 4 + 32 * len(SPEND_FIELDS):
        raise ReceiptError(f"{tx['hash']} has no canonical settlement frame")
    if frames[0]["status"] != 1:
        raise ReceiptError(f"{tx['hash']}'s settlement did not succeed")
    data = frames[0]["data"][4:]
    spend = {name: int.from_bytes(data[32 * i:32 * i + 32], "big") for i, name in enumerate(SPEND_FIELDS)}
    spend["outputs"] = [appended(l) for l in frames[0]["logs"] if _is(l, pool, LEAF_APPENDED)]
    return spend


def verify(chain, receipt, pool_check):
    """Check every note against the chain and summarize each spend it names.
    pool_check(pool) must authenticate the pool, since any contract can emit
    logs shaped like its own. Raises ReceiptError on the first failed claim."""
    try:
        return _verify(chain, receipt, pool_check)
    except (AttributeError, KeyError, TypeError, ValueError) as error:
        raise ReceiptError(f"malformed receipt: {error!r}") from None


def _verify(chain, receipt, pool_check):
    if receipt.get("receipt") != RECEIPT or receipt.get("version") != VERSION:
        raise ReceiptError("not a version 1 disclosure receipt")
    chain_id, pool = int(receipt["chainId"]), int(receipt["pool"], 16)
    if chain.chain_id() != chain_id:
        raise ReceiptError(f"the RPC is not chain {chain_id}")
    pool_check(pool)
    txs, spends, notes = {}, {}, []

    def tx(h):
        if h not in txs:
            txs[h] = chain.transaction(h)
        return txs[h]

    def spend_of(h):
        if h not in spends:
            spends[h] = decode_spend(tx(h), pool)
        return spends[h]

    for n in receipt["notes"]:
        cm, epoch, index, value = int(n["cm"], 16), int(n["epoch"]), int(n["index"]), int(n["value"])
        label = f"note {n['cm'][:18]}..."
        if any((m["cm"], m["epoch"], m["index"]) == (hex32(cm), epoch, index) for m in notes):
            raise ReceiptError(f"{label} is listed twice")  # it would count twice
        if not 0 <= value < w.MAX_VALUE or tagged(TAG_LEAF, int(n["inner"], 16), value) != cm:
            raise ReceiptError(f"{label}: the opening does not match the commitment")
        seen = {"cm": hex32(cm), "epoch": epoch, "index": index, "value": str(value)}
        if n.get("dummy"):
            if value != 0 or "spent" not in n:
                raise ReceiptError(f"{label}: a dummy input has value 0 and a spend")
            seen["origin"] = "dummy input"
        else:
            h = n["created"].lower()
            created = tx(h)
            emitted = [l for f in created["frames"] if f["status"] == 1 for l in f["logs"]] \
                if created["frames"] else created["logs"]
            if (cm, epoch, index) not in [appended(l) for l in emitted if _is(l, pool, LEAF_APPENDED)]:
                raise ReceiptError(f"{label}: {h} did not create it at epoch {epoch} leaf {index}")
            if created["sender"] != pool:
                seen["origin"] = f"deposit in {h}, sent by 0x{created['sender']:040x}"
            elif (cm, epoch, index) in spend_of(h)["outputs"]:
                seen["origin"] = f"output of {h}"
            else:  # a spend's fourth frame can call a contract that shields
                seen["origin"] = f"deposit made from {h}'s fourth frame"
        if "spent" in n:
            h = n["spent"].lower()
            spend = spend_of(h)
            if spend["epoch"] != epoch:
                raise ReceiptError(f"{label}: {h} spends epoch {spend['epoch']}, not {epoch}")
            nf = nullifier(int(n["nullifierKey"], 16), cm, index)
            if nf not in (spend["nf1"], spend["nf2"]):
                raise ReceiptError(f"{label}: its nullifier is not one {h} spent")
            seen["spent"], seen["nf"] = h, nf
        notes.append(seen)

    summary = {}
    for h, s in spends.items():
        inputs = [n for n in notes if n.get("spent") == h]
        if not inputs:
            continue
        shown = {(n["cm"], n["epoch"], n["index"]): n["value"] for n in notes if n["origin"] == f"output of {h}"}
        summary[h] = {"complete": {s["nf1"], s["nf2"]} <= {n["nf"] for n in inputs},
                      "inputValue": str(sum(int(n["value"]) for n in inputs)),
                      "outputs": [{"cm": hex32(c), "index": i, "value": shown.get((hex32(c), e, i))}
                                  for c, e, i in s["outputs"]],
                      "publicAmount": str(s["publicAmount"]), "fee": str(s["fee"]),
                      "recipient": f"0x{s['recipient']:040x}" if s["publicAmount"] else None}
    for n in notes:
        n.pop("nf", None)
    return {"chainId": chain_id, "pool": f"0x{pool:040x}", "notes": notes, "spends": summary}


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["export", "verify"])
    parser.add_argument("--rpc", required=True)
    parser.add_argument("--config", required=True, help="deployment config naming the pool")
    parser.add_argument("--fixture", help="export: the wallet fixture holding the openings")
    parser.add_argument("--only", help="export: comma-separated commitment prefixes to disclose")
    parser.add_argument("--output", help="export: where to write the receipt")
    parser.add_argument("--receipt", help="verify: the receipt to check")
    args = parser.parse_args()
    cfg, chain = json.loads(Path(args.config).read_text()), RpcChain(args.rpc)
    try:
        if args.command == "export":
            if not args.fixture or not args.output or Path(args.output).exists():
                raise ReceiptError("export needs --fixture and a new --output path")
            receipt = export(chain, int(cfg["chainId"]), int(cfg["pool"], 16),
                             json.loads(Path(args.fixture).read_text()),
                             args.only.split(",") if args.only else None, int(cfg.get("deploymentBlock", 0)))
            Path(args.output).write_text(json.dumps(receipt, indent=1) + "\n")
            print(f"wrote {args.output}: {len(receipt['notes'])} notes")
        else:
            sys.path.insert(0, str(HERE.parent / "devnet"))
            from pool_frametx import check_deployed_profile

            def pool_check(pool):
                if pool != int(cfg["pool"], 16):
                    raise ReceiptError("the receipt names another pool than the config")
                check_deployed_profile(args.rpc, pool, int(cfg["chainId"]),
                                       int(cfg["logic"], 16), int(cfg["verifier"], 16))
            receipt = json.loads(Path(args.receipt).read_text()) if args.receipt else None
            if not isinstance(receipt, dict):
                raise ReceiptError("verify needs --receipt naming a disclosure receipt")
            print(json.dumps(verify(chain, receipt, pool_check), indent=1))
    except ReceiptError as error:
        raise SystemExit(f"receipt rejected: {error}") from None


if __name__ == "__main__":
    main()
