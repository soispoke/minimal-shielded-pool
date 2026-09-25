#!/usr/bin/env python3
"""Disclosure receipts verify only what the chain shows and reject every
altered claim. The chain here is a small in-memory copy of what the pool
emits after a proof verifies: LeafAppended, NoteSpent, WithdrawalCredited
and a claim's Withdrawn, in the frames that emit them.
Run: python3 wallet/test_disclosure.py."""
import copy
import io
import json
import sys
from contextlib import redirect_stderr
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import disclosure as d  # noqa: E402
import wallet as w  # noqa: E402
from poseidon_bn254 import hex32  # noqa: E402

CHAIN, POOL, OTHER_POOL = 8141, 0xCB83980F3CC99E258295814375B0A94FE0AC0E86, 0x1111
ALICE, RECIPIENT = 0xA11CE, 0x9271FB610BC81B0D7026BE5D33A32B1FCFDA8926
ETH = 10**18


def log(address, first, *topics, data=0):
    return {"address": f"0x{address:040x}", "topics": [first, *[hex32(t) for t in topics]],
            "data": "0x" + data.to_bytes(32, "big").hex() if isinstance(data, int) else data}


def leaf(cm, epoch, index):
    return log(POOL, d.LEAF_APPENDED, cm, epoch, data="0x" + index.to_bytes(32, "big").hex() + "00" * 32)


class Chain:
    def __init__(self):
        self.id, self.txs = CHAIN, {}

    def chain_id(self):
        return self.id

    def add(self, h, sender, frames):
        self.txs[h] = {"hash": h, "sender": sender, "frames": frames,
                       "logs": [l for f in frames if f["status"] == 1 for l in f["logs"]]}

    def transaction(self, h):
        if h not in self.txs:
            raise d.ReceiptError(f"transaction {h} is not on this chain")
        return copy.deepcopy(self.txs[h])

    def logs(self, address, topics, from_block=0):
        def matches(have, want):
            return any(have.lower() == t.lower() for t in (want if isinstance(want, list) else [want]))
        return [dict(l, tx=h) for h, tx in self.txs.items() for l in tx["logs"]
                if int(l["address"], 16) == address
                and all(matches(l["topics"][i], t) for i, t in enumerate(topics))]


def settle_frame(spend, logs, status=1):
    data = d.SETTLE_SELECTOR + b"".join(spend[k].to_bytes(32, "big") for k in d.SPEND_FIELDS)
    return {"mode": 2, "to": POOL, "data": data, "status": status, "logs": logs if status else []}


def story():
    """Alice deposits 1 ETH, pays Bob 0.6 privately keeping 0.35 change, then
    withdraws 0.3 of the change to a recipient whose claim also collects 0.2 of
    earlier credit. She also deposits an identical note again, left unspent."""
    w.set_seed(7)
    D = w.domain_scalar(CHAIN, f"0x{POOL:040x}", 0)
    a, b, c, d1, d2, e = (w.new_note() for _ in range(6))
    cm = {k: w.commitment(*n, v) for k, n, v in
          (("a", a, ETH), ("b", b, 6 * ETH // 10), ("c", c, 35 * ETH // 100), ("d1", d1, 0), ("d2", d2, 0),
           ("e", e, 5 * ETH))}
    nf = {"a": w.nullifier(D, a[0], cm["a"], 0), "d1": w.nullifier(D, d1[0], cm["d1"], 0),
          "c": w.nullifier(D, c[0], cm["c"], 2), "d2": w.nullifier(D, d2[0], cm["d2"], 0)}
    sinks = w.sink_commitments()
    chain = Chain()
    shield = lambda index: [{"mode": 1, "to": ALICE, "data": b"", "status": 1, "logs": []},  # noqa: E731
                            {"mode": 2, "to": POOL, "data": b"", "status": 1, "logs": [leaf(cm["a"], 0, index)]}]
    chain.add("0xdep0", ALICE, shield(0))
    base = {"root": 1, "rootSlot": 5, "epoch": 0, "domain": D, "authorizer": 0xAAAA}
    transfer = dict(base, nf1=nf["a"], nf2=nf["d1"], outCm1=cm["b"], outCm2=cm["c"],
                    publicAmount=0, fee=5 * ETH // 100, recipient=0)
    chain.add("0xtransfer", POOL, [settle_frame(transfer, [
        log(POOL, d.NOTE_SPENT, nf["a"]), log(POOL, d.NOTE_SPENT, nf["d1"]),
        leaf(cm["b"], 0, 1), leaf(cm["c"], 0, 2)])])
    withdraw = dict(base, nf1=nf["c"], nf2=nf["d2"], outCm1=sinks[0], outCm2=sinks[1],
                    publicAmount=3 * ETH // 10, fee=5 * ETH // 100, recipient=RECIPIENT)
    chain.add("0xwithdraw", POOL, [
        settle_frame(withdraw, [log(POOL, d.NOTE_SPENT, nf["c"]), log(POOL, d.NOTE_SPENT, nf["d2"]),
                                log(POOL, d.WITHDRAWAL_CREDITED, RECIPIENT, data=3 * ETH // 10)]),
        # The fourth frame claims, then a contract it calls shields 5 ETH.
        {"mode": 0, "to": POOL, "data": b"", "status": 1,
         "logs": [log(POOL, d.WITHDRAWN, RECIPIENT, data=5 * ETH // 10), leaf(cm["e"], 0, 4)]}])
    chain.add("0xdep3", ALICE, shield(3))
    # After a rollover the same commitment can land at the same leaf of epoch 1.
    chain.add("0xdep_epoch1", ALICE, [{"mode": 2, "to": POOL, "data": b"", "status": 1,
                                        "logs": [leaf(cm["a"], 1, 0)]}])
    op = lambda n, v, leaf_: {"spend_key": hex32(n[0]), "rho": hex32(n[1]), "value": str(v), "leaf": leaf_}  # noqa: E731
    fixture = {"transfer": {"epoch": 0, "inputs": [op(a, ETH, 0), op(d1, 0, None)],
                            "output_openings": [op(b, 6 * ETH // 10, None), op(c, 35 * ETH // 100, None)]},
               "withdraw": {"epoch": 0, "inputs": [op(c, 35 * ETH // 100, 2), op(d2, 0, None)]}}
    return chain, fixture, {"a": a, "b": b, "c": c, "d1": d1, "d2": d2, "e": e}, cm


def export(chain, notes, only=None):
    with redirect_stderr(io.StringIO()) as err:
        receipt = d.export(chain, CHAIN, POOL, notes, only)
    return receipt, err.getvalue()


def trusted(pool):
    if pool != POOL:
        raise d.ReceiptError("the receipt names another pool than the config")


def verify(chain, receipt):
    return d.verify(chain, receipt, trusted)


def rejected(chain, receipt, expected):
    try:
        verify(chain, receipt)
    except d.ReceiptError as error:
        assert expected in str(error), (expected, str(error))
        return 1
    raise AssertionError(f"accepted a receipt that should fail: {expected}")


def note(receipt, cm, index=None):
    return next(n for n in receipt["notes"] if int(n["cm"], 16) == cm
                and (index is None or n["index"] == index))


def main():
    checked = 0
    chain, fixture, keys, cm = story()
    notes = d.openings(fixture)
    notes[cm["a"]]["places"] = set()  # the wallet knows the note, not which deposit
    receipt, _ = export(chain, notes)
    report = verify(chain, receipt)

    # The honest receipt traces the deposit through the transfer to the
    # withdrawal, and discloses both dummies, so each spend is fully explained.
    assert {(n["origin"].split()[0], n.get("spent")) for n in report["notes"]} == {
        ("deposit", "0xtransfer"), ("deposit", None), ("output", None), ("output", "0xwithdraw"),
        ("dummy", "0xtransfer"), ("dummy", "0xwithdraw")}
    t, wd = report["spends"]["0xtransfer"], report["spends"]["0xwithdraw"]
    assert t["complete"] and t["inputValue"] == str(ETH)
    assert [o["value"] for o in t["outputs"]] == [str(6 * ETH // 10), str(35 * ETH // 100)]
    assert wd["complete"] and wd["recipient"] == f"0x{RECIPIENT:040x}" and wd["outputs"] == []
    # The claim paid more than this withdrawal credited; it is reported as is.
    assert wd["claimedInSameTransaction"] == str(5 * ETH // 10)
    checked += 1

    # No spending secret leaves the wallet.
    text = json.dumps(receipt)
    for sk, rho in keys.values():
        assert hex32(sk) not in text and hex32(rho) not in text
    checked += 1

    def altered(path, value, expected, base=receipt):
        forged = copy.deepcopy(base)
        target = note(forged, *path)
        if value is None:
            target.pop(expected[0])
            expected = expected[1]
        else:
            target.update(value)
        return rejected(chain, forged, expected)

    other_key = hex32(d.nullifier_key(0, 1))
    checked += altered((cm["a"], 0), {"nullifierKey": other_key}, "not one 0xtransfer spent")
    checked += altered((cm["a"], 0), {"index": 1}, "did not create it")
    checked += altered((cm["a"], 0), {"value": str(2 * ETH)}, "opening does not match")
    checked += altered((cm["a"], 0), {"epoch": 1}, "did not create it")
    checked += altered((cm["a"], 0), {"spent": "0xwithdraw"}, "not one 0xwithdraw spent")
    checked += altered((cm["a"], 0), {"created": "0xdep3"}, "did not create it")
    # An identical deposit at another leaf has its own nullifier.
    key_a = note(receipt, cm["a"], 0)["nullifierKey"]
    checked += altered((cm["a"], 3), {"spent": "0xtransfer", "nullifierKey": key_a}, "not one 0xtransfer spent")
    checked += altered((cm["a"], 0), {"epoch": 1, "created": "0xdep_epoch1"}, "spends epoch 0, not 1")
    checked += altered((cm["d1"],), {"value": "1"}, "opening does not match")
    checked += altered((cm["d1"],), None, ("spent", "a dummy input has value 0 and a spend"))

    # Settlement must have succeeded, in a spend the pool sent, on this chain.
    failed = copy.deepcopy(chain)
    failed.txs["0xtransfer"]["frames"][0]["status"] = 0
    deposit_only, _ = export(chain, d.openings(fixture), only=[hex32(cm["a"])])
    checked += rejected(failed, deposit_only, "settlement did not succeed")
    impostor = copy.deepcopy(chain)
    impostor.txs["0xtransfer"]["sender"] = ALICE
    checked += rejected(impostor, receipt, "not a spend of this pool")
    elsewhere = copy.deepcopy(chain)
    elsewhere.id = 1
    checked += rejected(elsewhere, receipt, "not chain 8141")
    checked += rejected(chain, dict(receipt, pool=f"0x{OTHER_POOL:040x}"), "another pool than the config")
    checked += rejected(chain, {"receipt": d.RECEIPT, "version": 1, "chainId": CHAIN, "pool": f"0x{POOL:040x}", "notes": [{"cm": "0x1"}]}, "malformed")
    checked += rejected(chain, dict(receipt, version=2), "not a version 1 disclosure receipt")
    # A reverted frame's logs are not evidence, even if an RPC returns them.
    reverted = copy.deepcopy(chain)
    reverted.txs["0xtransfer"]["frames"][0]["status"] = 0
    bob_only, _ = export(chain, d.openings([{"inner": hex32(w.inner(*keys["b"])), "value": str(6 * ETH // 10)}]))
    checked += rejected(reverted, bob_only, "did not create it")
    truncated = copy.deepcopy(chain)
    truncated.txs["0xtransfer"]["frames"][0]["data"] = truncated.txs["0xtransfer"]["frames"][0]["data"][:-32]
    checked += rejected(truncated, deposit_only, "no canonical settlement frame")
    missing = copy.deepcopy(chain)
    del missing.txs["0xwithdraw"]
    checked += rejected(missing, receipt, "not on this chain")

    # Hiding Bob's output still shows its value when both inputs are disclosed:
    # conservation fixes it. The report says so, since that is what a reader learns.
    hidden, _ = export(chain, d.openings(fixture), only=[hex32(cm["a"]), hex32(cm["d1"]), hex32(cm["c"])])
    outs = verify(chain, hidden)["spends"]["0xtransfer"]["outputs"]
    assert outs[0]["value"] is None and outs[0]["impliedValue"] == str(6 * ETH // 10)
    checked += 1

    # Disclosing only the deposit links it to the transfer without explaining
    # the transfer's other input.
    partial, _ = export(chain, d.openings(fixture), only=[hex32(cm["a"])])
    s = verify(chain, partial)["spends"]["0xtransfer"]
    assert s["inputsDisclosed"] == 1 and not s["complete"] and "impliedValue" not in s["outputs"][0]
    checked += 1

    # A payer who knows only Bob's inner and value can show what Bob received.
    paid, _ = export(chain, d.openings([{"inner": hex32(w.inner(*keys["b"])), "value": str(6 * ETH // 10)}]))
    assert [n["index"] for n in paid["notes"]] == [1] and "nullifierKey" not in paid["notes"][0]
    assert verify(chain, paid)["notes"][0]["origin"] == "output of 0xtransfer"
    checked += 1

    # Two notes under one spend key share a nullifier key per epoch, so the
    # export warns that disclosing one exposes the other's nullifier.
    shared = [{"spend_key": hex32(keys["a"][0]), "rho": hex32(r), "value": "1", "epoch": 0, "index": None}
              for r in (1, 2)]
    _, warning = export(chain, d.openings(shared))
    assert "owns several notes" in warning
    checked += 1

    # Listing a note twice would count its value twice.
    doubled = copy.deepcopy(receipt)
    doubled["notes"].append(copy.deepcopy(note(receipt, cm["a"], 0)))
    checked += rejected(chain, doubled, "listed twice")
    # Hash spelling does not split one spend into two.
    shouting = copy.deepcopy(receipt)
    for n in shouting["notes"]:
        n.update({k: n[k].upper().replace("0X", "0x") for k in ("created", "spent") if k in n})
    assert set(verify(chain, shouting)["spends"]) == {"0xtransfer", "0xwithdraw"}
    checked += 1
    checked += rejected(chain, [receipt], "not a disclosure receipt")

    # A note shielded by a contract the withdrawal's fourth frame called is a
    # deposit, not an output of that withdrawal.
    tail, _ = export(chain, d.openings([{"inner": hex32(w.inner(*keys["e"])), "value": str(5 * ETH)}]))
    tail_report = verify(chain, tail)
    assert tail_report["notes"][0]["origin"] == "deposit made by a call in 0xwithdraw's fourth frame"
    assert verify(chain, receipt)["spends"]["0xwithdraw"]["outputs"] == []
    checked += 1

    # A known position selects that occurrence only, by epoch as well as leaf,
    # and every leaf a wallet names for one commitment is kept.
    known, _ = export(chain, d.openings(fixture), only=[hex32(cm["a"])])
    assert [(n["epoch"], n["index"]) for n in known["notes"] if n.get("created")] == [(0, 0)]
    both, _ = export(chain, d.openings([
        {"spend_key": hex32(keys["a"][0]), "rho": hex32(keys["a"][1]), "value": str(ETH), "epoch": 0, "index": i}
        for i in (3, 0)]))
    assert sorted(n["index"] for n in both["notes"]) == [0, 3]
    checked += 1

    # The RPC reader resolves a frame with no target to the sender, and turns
    # an unexpected response into a rejection rather than a crash.
    class Replay(d.RpcChain):
        def __init__(self, tx, receipt_):
            self.answers = {"eth_getTransactionByHash": tx, "eth_getTransactionReceipt": receipt_}

        def call(self, method, params):
            return self.answers[method]
    frame = chain.txs["0xtransfer"]["frames"][0]
    rpc_tx = {"sender": f"0x{POOL:040x}", "frames": [{"mode": "0x2", "to": None, "data": "0x" + frame["data"].hex()}]}
    rpc_receipt = {"logs": frame["logs"], "frameReceipts": [{"status": "0x1", "logs": frame["logs"]}]}
    assert d.decode_spend(Replay(rpc_tx, rpc_receipt).transaction("0xtransfer"), POOL)["nf1"] == \
        d.decode_spend(chain.transaction("0xtransfer"), POOL)["nf1"]
    try:
        Replay({"frames": [{"mode": "zz"}]}, rpc_receipt).transaction("0xbad")
    except d.ReceiptError as error:
        assert "unexpected RPC response" in str(error)
    else:
        raise AssertionError("a malformed RPC response was accepted")
    checked += 1

    print(f"PASS: {checked} disclosure checks: honest receipts verify, altered keys, positions, "
          "values, epochs, transactions, chains and pools are rejected")


if __name__ == "__main__":
    main()
