#!/usr/bin/env python3
"""Disclosure receipts: show which notes a spend consumed and created, without
giving away the spending key.

A note's nullifier is Poseidon3(4, K, Poseidon2(cm, index)), where the
nullifier key K = Poseidon2(D, spend_key) and D is the pool's domain for the
note's epoch. Given K and the note's position, anyone can recompute the
nullifier and find the spend that published it. Poseidon's collision
resistance and the spend proof tie that nullifier to exactly this note. K
cannot spend anything, because a spend proof needs spend_key itself, and the
wallet makes a fresh spend_key for each note, so K concerns only its note.

A receipt lists disclosed notes: each note's position and commitment, its
opening (inner, value) to prove the amount, the transaction that created it,
and, if it was spent, the spend and K. Following notes from spend to spend
traces funds from a public deposit through private transfers to a
withdrawal. A spend whose two inputs are both disclosed is fully explained,
since the circuit enforces conservation.

A receipt proves these links and amounts. It does not prove who presents it,
that they own the notes, or where the funds came from before the deposit.

  disclosure.py export --rpc URL --config CONFIG --notes FILE [--only CM,...] --output PATH
  disclosure.py verify --rpc URL --receipt PATH --config CONFIG [--json]

NOTES is a generator fixture or a list of openings, each {spend_key, rho,
value, epoch, index} for the owner's notes or {inner, value} for a note the
presenter paid but does not own; index may be null for a dummy input or a
note whose position the chain will tell. The receipt never contains
spend_key or rho.
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

RECEIPT = "minimal-shielded-pool/disclosure"
VERSION = 1
SPEND_TUPLE = "(bytes32,uint64,uint64,bytes32,bytes32,bytes32,bytes32,bytes32,uint256,uint256,address,address)"
SETTLE_SELECTOR = keccak(f"settle({SPEND_TUPLE})".encode())[:4]
SPEND_FIELDS = ("root", "rootSlot", "epoch", "domain", "nf1", "nf2", "outCm1", "outCm2",
                "publicAmount", "fee", "recipient", "authorizer")
SENDER_MODE = 2


def topic(signature):
    return "0x" + keccak(signature.encode()).hex()


LEAF_APPENDED = topic("LeafAppended(bytes32,uint64,uint32,bytes32)")
NOTE_SPENT = topic("NoteSpent(bytes32)")
WITHDRAWAL_CREDITED = topic("WithdrawalCredited(address,uint256)")
WITHDRAWN = topic("Withdrawn(address,uint256)")


class ReceiptError(Exception):
    """The receipt does not hold against the chain, or the chain could not be read."""


def nullifier_key(domain, spend_key):
    return p2(domain, spend_key)


def nullifier_from_key(key, cm, index):
    return tagged(w.TAG_OCCURRENCE_NULL, key, p2(cm, index))


class RpcChain:
    """The few chain reads a receipt needs, from a JSON-RPC endpoint."""

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
            sender = int(tx.get("sender") or tx["from"], 16)
            # A frame with no target calls the transaction's sender.
            frames = [{"mode": int(f["mode"], 16), "to": int(f["to"], 16) if f.get("to") else sender,
                       "data": bytes.fromhex(f["data"][2:]), "status": int(r["status"], 16),
                       "logs": r["logs"]}
                      for f, r in zip(tx.get("frames") or [], receipt.get("frameReceipts") or [])]
            return {"hash": tx_hash, "sender": sender, "frames": frames, "logs": receipt["logs"]}
        except (KeyError, TypeError, ValueError) as error:
            raise ReceiptError(f"unexpected RPC response for {tx_hash}: {error!r}") from None

    def logs(self, address, topics, from_block=0):
        found = self.call("eth_getLogs", [{"address": f"0x{address:040x}", "topics": topics,
                                           "fromBlock": hex(from_block), "toBlock": "latest"}])
        return [{"tx": l["transactionHash"].lower(), "address": l["address"], "topics": l["topics"],
                 "data": l["data"]} for l in found]


def _is(log, address, first_topic):
    topics = log.get("topics") or []
    return int(log["address"], 16) == address and topics and topics[0].lower() == first_topic


def appended(log):
    """(cm, epoch, index) of a LeafAppended log."""
    return int(log["topics"][1], 16), int(log["topics"][2], 16), int(log["data"][2:66], 16)


# ---- export ----

def openings(source):
    """Note openings from a notes list or a generator fixture, one per
    commitment, with every position a mention names."""
    found = {}

    def add(sk, rho, value, epoch, index, inner=None):
        # The same note can appear as one spend's output and another's input,
        # and one commitment can occupy several leaves. Keep what each mention
        # knows: the key, and each (epoch, index) it names. A dummy's
        # nullifier uses index 0 unless its opening says otherwise.
        inner = w.inner(sk, rho) if inner is None else inner
        note = found.setdefault(tagged(TAG_LEAF, inner, value),
                                {"sk": None, "inner": inner, "value": value, "places": set()})
        if note["sk"] is None:
            note["sk"] = sk
        if index is not None or value == 0:
            note["places"].add((epoch, 0 if index is None else int(index)))

    if isinstance(source, list):
        for n in source:
            epoch = None if n.get("epoch") is None else int(n["epoch"])
            if "spend_key" in n:
                add(int(n["spend_key"], 16), int(n["rho"], 16), int(n["value"]), epoch, n.get("index"))
            else:
                add(None, None, int(n["value"]), epoch, n.get("index"), int(n["inner"], 16))
        return found
    for entry in source.values():
        if not isinstance(entry, dict) or "inputs" not in entry:
            continue
        epoch = int(entry["epoch"])
        for i in entry["inputs"]:
            add(int(i["spend_key"], 16), int(i["rho"], 16), int(i["value"]), epoch, i["leaf"])
        for o in entry.get("output_openings", []):
            add(int(o["spend_key"], 16), int(o["rho"], 16), int(o["value"]), None, None)
    return found


def export(chain, chain_id, pool, notes, only=None, from_block=0):
    """A receipt for the given openings. It reads all of the pool's
    LeafAppended and NoteSpent logs once and matches them locally, so the RPC
    does not learn which notes are being disclosed."""
    if chain.chain_id() != chain_id:
        raise ReceiptError("the RPC is not on the configured chain")
    leaves, spent_in = {}, {}
    for log in chain.logs(pool, [[LEAF_APPENDED, NOTE_SPENT]], from_block):
        if log["topics"][0].lower() == LEAF_APPENDED:
            cm, epoch, index = appended(log)
            leaves.setdefault(cm, []).append((epoch, index, log["tx"]))
        else:
            spent_in.setdefault(int(log["topics"][1], 16), log["tx"])
    keys = {}
    for n in notes.values():
        if n["sk"] is not None:
            keys.setdefault(n["sk"], []).append(n)
    if any(len(ns) > 1 for ns in keys.values()):
        print("warning: a spend key owns several notes; its nullifier key exposes each of their "
              "nullifiers in the same epoch", file=sys.stderr)
    out = []
    for cm, n in sorted(notes.items(), key=lambda item: (item[1]["value"] == 0, item[0])):
        if only and not any(hex32(cm).startswith(prefix.lower()) for prefix in only):
            continue
        if n["value"] == 0:
            # A dummy input is never in the tree; only its spend can be shown.
            if n["sk"] is None:
                continue
            places = [(epoch, index, None) for epoch, index in n["places"] if epoch is not None]
        else:
            places = [(e, i, h) for e, i, h in leaves.get(cm, [])
                      if not n["places"] or any(i == pi and pe in (None, e) for pe, pi in n["places"])]
            if not places:
                print(f"skipped {hex32(cm)[:18]}...: not in the pool's tree", file=sys.stderr)
        for epoch, index, created in places:
            spent = key = None
            if n["sk"] is not None:
                key = nullifier_key(w.domain_scalar(chain_id, pool, epoch), n["sk"])
                spent = spent_in.get(nullifier_from_key(key, cm, index))
            if n["value"] == 0 and spent is None:
                continue
            note = {"epoch": epoch, "index": index, "cm": hex32(cm), "inner": hex32(n["inner"]),
                    "value": str(n["value"])}
            if n["value"] == 0:
                note["dummy"] = True
            else:
                note["created"] = created
            if spent is not None:
                note["spent"] = spent
                note["nullifierKey"] = hex32(key)
            out.append(note)
    return {"receipt": RECEIPT, "version": VERSION, "chainId": chain_id,
            "pool": f"0x{pool:040x}", "notes": out}


# ---- verify ----

def decode_spend(tx, pool):
    """The settlement fields and inserted outputs of a pool spend, or ReceiptError."""
    if tx["sender"] != pool:
        raise ReceiptError(f"{tx['hash']} is not a spend of this pool")
    frames = [f for f in tx["frames"]
              if f["mode"] == SENDER_MODE and f["to"] == pool and f["data"][:4] == SETTLE_SELECTOR]
    if len(frames) != 1 or len(frames[0]["data"]) != 4 + 32 * len(SPEND_FIELDS):
        raise ReceiptError(f"{tx['hash']} has no canonical settlement frame")
    frame = frames[0]
    if frame["status"] != 1:
        raise ReceiptError(f"{tx['hash']}'s settlement did not succeed")
    data = frame["data"][4:]
    spend = {name: int.from_bytes(data[32 * i:32 * i + 32], "big") for i, name in enumerate(SPEND_FIELDS)}
    spend["outputs"] = [appended(l) for l in frame["logs"] if _is(l, pool, LEAF_APPENDED)]
    return spend


def verify(chain, receipt, pool_check):
    """Check every note in a receipt against the chain and summarize each spend.
    pool_check(pool) must authenticate the pool the receipt names: any contract
    can emit logs shaped like the pool's. Raises ReceiptError on the first claim
    that does not hold."""
    if not isinstance(receipt, dict):
        raise ReceiptError("not a disclosure receipt")
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
        cm, epoch, index = int(n["cm"], 16), int(n["epoch"]), int(n["index"])
        value = int(n["value"])
        label = f"note {n['cm'][:18]}..."
        # Each note counts once; a repeat would inflate the values below.
        if any((m["cm"], m["epoch"], m["index"]) == (cm, epoch, index) for m in notes):
            raise ReceiptError(f"{label} is listed twice")
        if not 0 <= value < w.MAX_VALUE or tagged(TAG_LEAF, int(n["inner"], 16), value) != cm:
            raise ReceiptError(f"{label}: the opening does not match the commitment")
        seen = {"cm": cm, "epoch": epoch, "index": index, "value": value}
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
                seen["origin"] = "output of " + h
            else:
                # A spend's fourth frame can call a contract that shields.
                seen["origin"] = f"deposit made by a call in {h}'s fourth frame"
        if "spent" in n:
            h = n["spent"].lower()
            spend = spend_of(h)
            if spend["epoch"] != epoch:
                raise ReceiptError(f"{label}: {h} spends epoch {spend['epoch']}, not {epoch}")
            nf = nullifier_from_key(int(n["nullifierKey"], 16), cm, index)
            if nf not in (spend["nf1"], spend["nf2"]):
                raise ReceiptError(f"{label}: its nullifier is not one {h} spent")
            seen["spent"], seen["nf"] = h, nf
        notes.append(seen)

    return {"chainId": chain_id, "pool": f"0x{pool:040x}", "notes": notes,
            "spends": {h: summarize(h, spend, notes, txs[h], pool)
                       for h, spend in spends.items() if any(n.get("spent") == h for n in notes)}}


def summarize(tx_hash, spend, notes, tx, pool):
    """What the receipt establishes about one spend."""
    inputs = [n for n in notes if n.get("spent") == tx_hash]
    by_nf = {n["nf"] for n in inputs}
    outputs = []
    for cm, epoch, index in spend["outputs"]:
        disclosed = [n for n in notes if (n["cm"], n["epoch"], n["index"]) == (cm, epoch, index)
                     and n["origin"] == "output of " + tx_hash]
        outputs.append({"cm": hex32(cm), "epoch": epoch, "index": index,
                        "value": str(disclosed[0]["value"]) if disclosed else None})
    complete = {spend["nf1"], spend["nf2"]} <= by_nf
    summary = {"inputsDisclosed": len(by_nf & {spend["nf1"], spend["nf2"]}), "complete": complete,
               "inputValue": str(sum(n["value"] for n in inputs)), "outputs": outputs,
               "publicAmount": str(spend["publicAmount"]), "fee": str(spend["fee"]),
               "recipient": f"0x{spend['recipient']:040x}" if spend["publicAmount"] else None}
    hidden = [o for o in outputs if o["value"] is None]
    if complete and len(hidden) == 1:
        # Conservation fixes the one undisclosed output's value.
        shown = sum(int(o["value"]) for o in outputs if o["value"] is not None)
        hidden[0]["impliedValue"] = str(sum(n["value"] for n in inputs) - shown
                                        - spend["publicAmount"] - spend["fee"])
    if spend["publicAmount"]:
        paid = [int(l["data"][2:66], 16) for f in tx["frames"] if f["status"] == 1 for l in f["logs"]
                if _is(l, pool, WITHDRAWN) and int(l["topics"][1], 16) == spend["recipient"]]
        # A claim pays everything credited to the recipient, which may include
        # other withdrawals, so it is reported, not attributed to this spend.
        summary["claimedInSameTransaction"] = str(sum(paid)) if paid else None
    return summary

def eth(wei):
    whole, frac = divmod(int(wei), 10**18)
    return f"{whole}.{frac:018d}".rstrip("0").rstrip(".") + " ETH"


def describe(report):
    lines = [f"receipt verified for pool {report['pool']} on chain {report['chainId']}"]
    for n in report["notes"]:
        line = f"  note {hex32(n['cm'])[:18]}... epoch {n['epoch']} leaf {n['index']}, {eth(n['value'])}: {n['origin']}"
        if "spent" in n:
            line += f", spent in {n['spent']}"
        lines.append(line)
    for h, s in report["spends"].items():
        lines.append(f"  spend {h}: {s['inputsDisclosed']} of 2 inputs disclosed"
                     f"{' (fully explained)' if s['complete'] else ''}, input value {eth(s['inputValue'])}, "
                     f"public amount {eth(s['publicAmount'])}, fee {eth(s['fee'])}")
        if s["recipient"]:
            claim = s["claimedInSameTransaction"]
            lines.append(f"    withdrawal credited to {s['recipient']}"
                         + (f"; a claim in the same transaction paid {eth(claim)}" if claim else "; not claimed in this transaction"))
        for o in s["outputs"]:
            value = eth(o["value"]) if o["value"] else (f"undisclosed, {eth(o['impliedValue'])} by conservation" if "impliedValue" in o
                                   else "undisclosed")
            lines.append(f"    output {o['cm'][:18]}... leaf {o['index']}: {value}")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    ex = sub.add_parser("export")
    ex.add_argument("--rpc", required=True)
    ex.add_argument("--config", required=True)
    ex.add_argument("--notes", required=True)
    ex.add_argument("--only", help="comma-separated commitment prefixes to disclose")
    ex.add_argument("--output", required=True)
    ve = sub.add_parser("verify")
    ve.add_argument("--rpc", required=True)
    ve.add_argument("--receipt", required=True)
    ve.add_argument("--config", required=True,
                    help="deployment config naming the pool, whose deployed code is checked")
    ve.add_argument("--json", action="store_true")
    args = parser.parse_args()
    chain = RpcChain(args.rpc)
    try:
        if args.command == "export":
            cfg = json.loads(Path(args.config).read_text())
            output = Path(args.output)
            if output.exists():
                raise ReceiptError(f"{output} exists")
            receipt = export(chain, int(cfg["chainId"]), int(cfg["pool"], 16),
                             openings(json.loads(Path(args.notes).read_text())),
                             args.only.split(",") if args.only else None, int(cfg.get("deploymentBlock", 0)))
            output.write_text(json.dumps(receipt, indent=1) + "\n")
            print(f"wrote {output}: {len(receipt['notes'])} notes")
        else:
            sys.path.insert(0, str(HERE.parent / "devnet"))
            from pool_frametx import check_deployed_profile
            cfg = json.loads(Path(args.config).read_text())

            def pool_check(pool):
                if pool != int(cfg["pool"], 16):
                    raise ReceiptError("the receipt names another pool than the config")
                check_deployed_profile(args.rpc, pool, int(cfg["chainId"]),
                                       int(cfg["logic"], 16), int(cfg["verifier"], 16))
            report = verify(chain, json.loads(Path(args.receipt).read_text()), pool_check)
            print(json.dumps(report, indent=1, default=str) if args.json else describe(report))
    except ReceiptError as error:
        raise SystemExit(f"receipt rejected: {error}") from None


if __name__ == "__main__":
    main()
