#!/usr/bin/env python3
"""Disclosure receipts verify only what the chain shows and reject every
altered claim. The chain here is a small in-memory copy of what the pool
emits after a proof verifies: LeafAppended and NoteSpent, in the frames that
emit them, plus the EIP-8250 keys spends consume.
Run: python3 wallet/test_disclosure.py."""
import copy
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import disclosure as d  # noqa: E402
import wallet as w  # noqa: E402
from poseidon_bn254 import hex32  # noqa: E402

CHAIN, POOL, ALICE, RECIPIENT = 8141, 0xCB83980F3CC99E258295814375B0A94FE0AC0E86, 0xA11CE, 0x9271FB61
ETH = 10**18


def log(first, *topics, data="0x"):
    return {"address": f"0x{POOL:040x}", "topics": [first, *[hex32(t) for t in topics]], "data": data}


def leaf(cm, epoch, index):
    return log(d.LEAF_APPENDED, cm, epoch, data="0x" + index.to_bytes(32, "big").hex() + "00" * 32)


class Chain:
    def __init__(self):
        self.id, self.txs, self.finalized, self.unindexed = CHAIN, {}, 10**9, set()

    def chain_id(self):
        return self.id

    def finalized_block(self):
        return self.finalized

    def add(self, h, sender, frames):
        self.txs[h] = {"hash": h, "sender": sender, "block": len(self.txs) + 1, "frames": frames,
                       "logs": [l for f in frames if f["status"] == 1 for l in f["logs"]]}

    def transaction(self, h):
        if h not in self.txs:
            raise d.ReceiptError(f"transaction {h} is not on this chain")
        return copy.deepcopy(self.txs[h])

    def logs(self, address, topics, from_block=0):
        # `unindexed` models ethrex leaving a transaction out of eth_getLogs.
        return [dict(l, tx=h) for h, tx in self.txs.items() if h not in self.unindexed for l in tx["logs"]
                if int(l["address"], 16) == address
                and all(l["topics"][i] in (t if isinstance(t, list) else [t]) for i, t in enumerate(topics))]

    def nonce_used(self, sender, key):
        return sender == POOL and any(l["topics"] == [d.NOTE_SPENT, hex32(key)]
                                      for tx in self.txs.values() for l in tx["logs"])


def frame(logs, data=b"", mode=2, status=1):
    return {"mode": mode, "to": POOL, "data": data, "status": status, "logs": logs}


def settle(spend, logs):
    return frame(logs, d.SETTLE_SELECTOR + b"".join(spend[k].to_bytes(32, "big") for k in d.SPEND_FIELDS))


def story():
    """Alice deposits 1 ETH, pays Bob 0.6 privately keeping 0.35 change, and
    withdraws 0.3 of the change; a contract the withdrawal's fourth frame calls
    shields 5 ETH. Bob later withdraws his note. The same commitment as Alice's
    deposit also lands at leaf 3, and at leaf 0 of epoch 1 after a rollover."""
    w.set_seed(7)
    D = w.domain_scalar(CHAIN, f"0x{POOL:040x}", 0)
    notes = {k: w.new_note() for k in ("a", "b", "c", "d1", "d2", "d3", "e")}
    values = {"a": ETH, "b": 6 * ETH // 10, "c": 35 * ETH // 100, "d1": 0, "d2": 0, "d3": 0, "e": 5 * ETH}
    cm = {k: w.commitment(*notes[k], values[k]) for k in notes}
    nf = {k: w.nullifier(D, notes[k][0], cm[k], i)
          for k, i in (("a", 0), ("d1", 0), ("c", 2), ("d2", 0), ("b", 1), ("d3", 0))}
    sinks = w.sink_commitments()
    chain = Chain()
    chain.add("0xdep0", ALICE, [frame([leaf(cm["a"], 0, 0)])])
    base = {"root": 1, "rootSlot": 5, "epoch": 0, "domain": D, "authorizer": 0xAAAA, "fee": 5 * ETH // 100}
    chain.add("0xtransfer", POOL, [settle(
        dict(base, nf1=nf["a"], nf2=nf["d1"], outCm1=cm["b"], outCm2=cm["c"], publicAmount=0, recipient=0),
        [log(d.NOTE_SPENT, nf["a"]), log(d.NOTE_SPENT, nf["d1"]), leaf(cm["b"], 0, 1), leaf(cm["c"], 0, 2)])])
    chain.add("0xwithdraw", POOL, [
        settle(dict(base, nf1=nf["c"], nf2=nf["d2"], outCm1=sinks[0], outCm2=sinks[1],
                    publicAmount=3 * ETH // 10, recipient=RECIPIENT),
               [log(d.NOTE_SPENT, nf["c"]), log(d.NOTE_SPENT, nf["d2"])]),
        frame([leaf(cm["e"], 0, 4)], mode=0)])
    chain.add("0xbobexit", POOL, [settle(dict(base, nf1=nf["b"], nf2=nf["d3"], outCm1=sinks[0], outCm2=sinks[1],
                                              publicAmount=55 * ETH // 100, recipient=0xB0B),
                                         [log(d.NOTE_SPENT, nf["b"]), log(d.NOTE_SPENT, nf["d3"])])])
    chain.add("0xdep3", ALICE, [frame([leaf(cm["a"], 0, 3)])])
    chain.add("0xdep_epoch1", ALICE, [frame([leaf(cm["a"], 1, 0)])])
    op = lambda k, leaf_=None: {"spend_key": hex32(notes[k][0]), "rho": hex32(notes[k][1]),  # noqa: E731
                                "value": str(values[k]), "leaf": leaf_}
    # Like the repository's generators, Alice's fixture also holds Bob's key.
    fixture = {"transfer": {"epoch": 0, "inputs": [op("a", 0), op("d1")], "output_openings": [op("b"), op("c")]},
               "withdraw": {"epoch": 0, "inputs": [op("c", 2), op("d2")]}}
    return chain, fixture, notes, cm, op


def trusted(pool):
    if pool != POOL:
        raise d.ReceiptError("the receipt names another pool than the config")


def verify(chain, receipt):
    return d.verify(chain, receipt, trusted)


def export(chain, fixture, only=None):
    return d.export(chain, CHAIN, POOL, fixture, only)


def rejected(chain, receipt, expected):
    try:
        verify(chain, receipt)
    except d.ReceiptError as error:
        assert expected in str(error), (expected, str(error))
        return 1
    raise AssertionError(f"accepted a receipt that should fail: {expected}")


def main():
    checked = 0
    chain, fixture, notes, cm, op = story()
    receipt = export(chain, fixture)
    report = verify(chain, receipt)

    # The receipt traces the deposit through the transfer to the withdrawal and
    # discloses both dummies, so each spend is fully explained.
    assert sorted((n["origin"].split()[0], n["spent"]) for n in report["notes"]) == sorted([
        ("deposit", "0xtransfer"), ("output", "not disclosed"), ("output", "0xwithdraw"),
        ("dummy", "0xtransfer"), ("dummy", "0xwithdraw")])
    t, wd = report["spends"]["0xtransfer"], report["spends"]["0xwithdraw"]
    assert t["complete"] and t["inputValue"] == str(ETH)
    assert [o["value"] for o in t["outputs"]] == [str(6 * ETH // 10), str(35 * ETH // 100)]
    assert wd["complete"] and wd["recipient"] == f"0x{RECIPIENT:040x}" and wd["outputs"] == []
    text = json.dumps(receipt)
    assert not any(hex32(x) in text for n in notes.values() for x in n), "a spending secret was exported"
    checked += 1

    def note(r, key, epoch=0, index=None):
        return next(n for n in r["notes"] if int(n["cm"], 16) == cm[key] and n["epoch"] == epoch
                    and (index is None or n["index"] == index))

    # Bob's note is only an output of Alice's payment, so his later withdrawal
    # stays his to disclose, although her fixture holds his key.
    assert "nullifierKey" not in note(receipt, "b") and "0xbobexit" not in text
    checked += 1

    def altered(key, change, expected, index=None, drop=None):
        forged = copy.deepcopy(receipt)
        target = note(forged, key, index=index)
        target.update(change)
        if drop:
            target.pop(drop)
        return rejected(chain, forged, expected)

    key_a = note(receipt, "a")["nullifierKey"]
    checked += altered("a", {"nullifierKey": hex32(12345)}, "not one 0xtransfer spent")
    checked += altered("a", {"index": 1}, "did not create it")
    checked += altered("a", {"value": str(2 * ETH)}, "opening does not match")
    checked += altered("a", {"epoch": 1}, "did not create it")
    checked += altered("a", {"epoch": 1, "created": "0xdep_epoch1"}, "spends epoch 0, not 1")
    checked += altered("a", {"spent": "0xwithdraw"}, "not one 0xwithdraw spent")
    checked += altered("a", {"created": "0xdep3"}, "did not create it")
    checked += altered("a", {"index": 3, "created": "0xdep3", "nullifierKey": key_a}, "not one 0xtransfer spent")
    checked += altered("d1", {"value": "1"}, "opening does not match")
    checked += altered("d1", {}, "a dummy input has value 0 and a spend", drop="spent")
    # A dummy's index is not in the tree, so index + P would alias its nullifier.
    checked += altered("d1", {"index": note(receipt, "d1")["index"] + w.P}, "outside the tree")

    doubled = copy.deepcopy(receipt)
    doubled["notes"].append(copy.deepcopy(note(receipt, "a")))
    checked += rejected(chain, doubled, "listed twice")
    checked += rejected(chain, dict(receipt, version=2), "not a version 1 disclosure receipt")
    checked += rejected(chain, dict(receipt, pool="0x1111"), "another pool than the config")
    checked += rejected(chain, dict(receipt, notes=[{"cm": "0x1"}]), "malformed")
    checked += rejected(chain, [receipt], "malformed")
    shouting = copy.deepcopy(receipt)
    for n in shouting["notes"]:
        n.update({k: n[k].upper().replace("0X", "0x") for k in ("created", "spent") if k in n})
    assert set(verify(chain, shouting)["spends"]) == {"0xtransfer", "0xwithdraw"}
    checked += 1

    # Settlement must have succeeded, in a canonical spend the pool sent, in a
    # finalized block, on this chain; logs from a reverted frame are not evidence.
    deposit_only = export(chain, fixture, {cm["a"]})
    for mutate, expected, r in (
            (lambda c: c.txs["0xtransfer"]["frames"][0].update(status=0), "settlement did not succeed", deposit_only),
            (lambda c: c.txs["0xtransfer"].update(sender=ALICE), "not a spend of this pool", deposit_only),
            (lambda c: c.txs["0xtransfer"]["frames"][0].update(data=c.txs["0xtransfer"]["frames"][0]["data"][:-32]),
             "no canonical settlement frame", deposit_only),
            (lambda c: setattr(c, "finalized", c.txs["0xdep0"]["block"]), "not finalized", deposit_only),
            (lambda c: setattr(c, "id", 1), "not chain 8141", receipt),
            (lambda c: c.txs.pop("0xwithdraw"), "not on this chain", receipt),
            (lambda c: c.txs["0xtransfer"]["frames"][0].update(status=0), "did not create it",
             dict(receipt, notes=[note(receipt, "b")]))):
        broken = copy.deepcopy(chain)
        mutate(broken)
        checked += rejected(broken, r, expected)

    # A node whose logs miss a spend, as ethrex does when a spend's fourth
    # frame fails, makes export fail rather than call the note unspent.
    gap = copy.deepcopy(chain)
    gap.unindexed.add("0xtransfer")
    try:
        export(gap, fixture, {cm["a"]})
    except d.ReceiptError as error:
        assert "logs do not show" in str(error)
        checked += 1
    else:
        raise AssertionError("an export missed a spend the chain consumed")

    # A deposit made from a spend's fourth frame is not one of its outputs.
    tail = export(chain, {"x": {"epoch": 0, "inputs": [], "output_openings": [op("e")]}})
    assert verify(chain, tail)["notes"][0]["origin"] == "deposit made from 0xwithdraw's fourth frame"
    checked += 1

    # A disclosed input with its partner hidden leaves the spend unexplained.
    assert not verify(chain, deposit_only)["spends"]["0xtransfer"]["complete"]
    checked += 1

    # An input names its leaf and epoch; a note known only by commitment
    # covers each leaf it occupies, without a nullifier key.
    assert [(n["epoch"], n["index"]) for n in deposit_only["notes"]] == [(0, 0)]
    anywhere = export(chain, {"x": {"epoch": 0, "inputs": [], "output_openings": [op("a")]}})
    assert sorted((n["epoch"], n["index"], "nullifierKey" in n) for n in anywhere["notes"]) == \
        [(0, 0, False), (0, 3, False), (1, 0, False)]
    checked += 1

    # The RPC reader resolves a frame with no target to the sender, and turns
    # an unexpected response into a rejection rather than a crash.
    class Replay(d.RpcChain):
        def __init__(self, tx, receipt_):
            self.answers = {"eth_getTransactionByHash": tx, "eth_getTransactionReceipt": receipt_}

        def call(self, method, params):
            return self.answers[method]
    spend = chain.txs["0xtransfer"]["frames"][0]
    rpc_tx = {"sender": f"0x{POOL:040x}", "frames": [{"mode": "0x2", "to": None, "data": "0x" + spend["data"].hex()}]}
    rpc_receipt = {"blockNumber": "0x1", "logs": spend["logs"],
                   "frameReceipts": [{"status": "0x1", "logs": spend["logs"]}]}
    assert d.decode_spend(Replay(rpc_tx, rpc_receipt).transaction("0x1"), POOL)["nf1"] == \
        d.decode_spend(chain.transaction("0xtransfer"), POOL)["nf1"]
    for bad_tx, bad_receipt in (({"frames": [{"mode": "zz"}]}, rpc_receipt),
                                (rpc_tx, dict(rpc_receipt, frameReceipts=[]))):
        try:
            Replay(bad_tx, bad_receipt).transaction("0xbad")
        except d.ReceiptError as error:
            assert "unexpected RPC response" in str(error)
            checked += 1
        else:
            raise AssertionError("a malformed RPC response was accepted")

    # Export discloses only what is named in full: a prefix could match notes
    # the user did not mean to disclose, and a disclosure cannot be taken back.
    import subprocess
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        cfg = Path(tmp, "config.json")
        cfg.write_text(json.dumps({"chainId": CHAIN, "pool": f"0x{POOL:040x}"}))
        base = [sys.executable, str(HERE / "disclosure.py"), "export", "--rpc", "http://127.0.0.1:1",
                "--config", str(cfg), "--fixture", str(cfg), "--output", str(Path(tmp, "r.json"))]
        for extra, expected in (([], "--only with the notes to disclose, or --all"),
                                (["--all", "--only", hex32(cm["a"])], "--only with the notes to disclose, or --all"),
                                (["--only", "0x"], "full commitments"),
                                (["--only", hex32(cm["a"]) + ","], "full commitments")):
            result = subprocess.run(base + extra, capture_output=True, text=True)
            assert result.returncode != 0 and expected in result.stderr, (extra, result.stderr[-300:])
            checked += 1

    # Receipts are created readable only by their owner, and never replace an
    # existing file or follow a link planted at the output path.
    import os
    import stat
    with tempfile.TemporaryDirectory() as tmp:
        old = os.umask(0o022)
        try:
            d.write_new_private(Path(tmp, "r.json"), "{}")
        finally:
            os.umask(old)
        assert stat.S_IMODE(Path(tmp, "r.json").stat().st_mode) == 0o600
        Path(tmp, "target").write_text("keep")
        Path(tmp, "link").symlink_to(Path(tmp, "target"))
        for existing in ("r.json", "link"):
            try:
                d.write_new_private(Path(tmp, existing), "new")
            except d.ReceiptError:
                checked += 1
            else:
                raise AssertionError(f"export replaced {existing}")
        assert Path(tmp, "target").read_text() == "keep" and Path(tmp, "r.json").read_text() == "{}"

    print(f"PASS: {checked} disclosure checks: honest receipts verify; altered keys, positions, values, "
          "epochs, transactions, chains and pools are rejected")


if __name__ == "__main__":
    main()
