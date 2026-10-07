#!/usr/bin/env python3
"""Note delivery: wallets find their notes and spends from their seed alone,
through a public address or a secret sent out of band, notes open for no one
else, senders cannot reuse an index or a ciphertext or outrun the recipient's
window, payments that land out of order are found, several pool calls in one
transaction are read apart, calls a node leaves out of eth_getLogs are rebuilt
from receipts or caught, and secrets stay in owner-only files. The chain is an
in-memory list of what the pool emits, and the CLI runs against a local
JSON-RPC server serving the same logs and receipts.
Run: python3 test/test_notes.py."""
import contextlib
import http.server
import io
import json
import os
import stat
import sys
import tempfile
import threading
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "sdk"))
import notes as n  # noqa: E402
import wallet as w  # noqa: E402
from gas_profile import POOL_PROFILE, SHIELD_NOTE_BYTES, SPEND_NOTES_BYTES  # noqa: E402
from poseidon_bn254 import hex32  # noqa: E402

CHAIN, POOL = 8141, 0xCB83980F3CC99E258295814375B0A94FE0AC0E86
ETH = 10**18
FEE = ETH // 100


def raises(fn, expected):
    try:
        fn()
    except n.NotesError as error:
        assert expected in str(error), (expected, str(error))
        return 1
    raise AssertionError(f"accepted input that should fail: {expected}")


class Chain:
    """The pool's events, one per shield or settlement, and the leaves of epoch 0.
    Each call gets its own block unless it shares the previous call's transaction."""

    def __init__(self):
        self.events, self.size, self.block = [], 0, 100

    def add(self, notes, outputs, spent=(), sizes=SPEND_NOTES_BYTES, same_tx=False, same_block=False, skip=0):
        assert len(notes) in sizes, len(notes)
        leaves = []
        for cm in outputs:
            leaves.append((cm, 0, self.size))
            self.size += 1
        if same_tx:
            last = self.events[-1]
            block, tx, call = last.block, last.tx, last.call + 1
        elif same_block:
            last = self.events[-1]
            block, tx, call = last.block, last.tx + 1, 0
        else:
            self.block += 1 + skip
            block, tx, call = self.block, self.block % 3, 0
        self.events.append(n.Event(block, notes, leaves, list(spent), tx=tx, call=call))
        return leaves


def paid(owner_pk, channel, value):
    """A note on `channel` for value, and the commitment it opens to."""
    note, rho, _, ciphertext = n.reserve(channel, value)
    return note, n.output_commitment(owner_pk, rho, value), ciphertext


ALICE, BOB, CAROL = (n.WalletKeys(w.keccak(name)) for name in (b"alice", b"bob", b"carol"))


def nullifier_of(keys, cm, index):
    return w.nullifier(w.domain_scalar(CHAIN, POOL, 0), keys.spend_key, cm, index)


def story():
    """Bob shields, pays Alice four ways, then spends his deposit and withdraws;
    Carol pays Bob through his address."""
    chain = Chain()
    bob_self = n.direct_channel(BOB.owner_pk, BOB.self_secret)
    carol_self = n.direct_channel(CAROL.owner_pk, CAROL.self_secret)
    note, cm, _ = paid(BOB.owner_pk, bob_self, 5 * ETH)
    deposit = chain.add(n.shield_notes(note), [cm], sizes=SHIELD_NOTE_BYTES)[0]

    # Bob pays Alice's public address. The first payment carries the ciphertext.
    to_alice = n.open_channel(ALICE.address().hex())
    payee, payee_cm, ciphertext = paid(ALICE.owner_pk, to_alice, ETH)
    change, change_cm, _ = paid(BOB.owner_pk, bob_self, 4 * ETH - FEE)
    spent = [nullifier_of(BOB, deposit[0], deposit[2]), 1]  # with a dummy input's nullifier
    chain.add(n.spend_notes(payee, change, ciphertext), [payee_cm, change_cm], spent)
    assert to_alice.ciphertext == ciphertext and to_alice.next_index == 1

    # Until that payment is final, the channel takes no other payment.
    raises(lambda: n.reserve(to_alice, ETH), "opening payment is not final yet")
    n.finalized(to_alice, 0)
    payee, payee_cm, ciphertext = paid(ALICE.owner_pk, to_alice, ETH // 2)
    assert ciphertext == b""
    change, change_cm, _ = paid(BOB.owner_pk, bob_self, 3 * ETH)
    chain.add(n.spend_notes(payee, change), [change_cm, payee_cm], [2, 3])

    # Alice handed Bob her third direct secret over Signal: nothing extra on chain.
    to_alice_direct = n.direct_channel(ALICE.owner_pk, ALICE.direct_secret(3))
    payee, payee_cm, _ = paid(ALICE.owner_pk, to_alice_direct, ETH // 5)
    change, change_cm, _ = paid(BOB.owner_pk, bob_self, 2 * ETH)
    chain.add(n.spend_notes(payee, change), [payee_cm, change_cm], [4, 5])

    # A withdrawal: the payee note is random and only the change is a leaf.
    change, change_cm, _ = paid(BOB.owner_pk, bob_self, ETH)
    chain.add(n.spend_notes(n.dummy_note(), change), [change_cm], [6, 7])

    # A shield straight to Alice's address, on a second secret.
    note, cm, ciphertext = paid(ALICE.owner_pk, n.open_channel(ALICE.address()), 2 * ETH)
    chain.add(n.shield_notes(note, ciphertext), [cm], sizes=SHIELD_NOTE_BYTES)

    # Carol's first payment to Alice never lands. Sending its ciphertext again in
    # another transaction would link the two, so she opens a new channel.
    lost = n.open_channel(ALICE.address())
    n.reserve(lost, ETH // 10)
    raises(lambda: n.reserve(lost, ETH // 10), "opening payment is not final yet")
    payee, payee_cm, ciphertext = paid(ALICE.owner_pk, n.open_channel(ALICE.address()), ETH // 10)
    change, change_cm, _ = paid(CAROL.owner_pk, carol_self, ETH // 3)
    chain.add(n.spend_notes(payee, change, ciphertext), [payee_cm, change_cm], [10, 11])

    # Carol pays Bob's address.
    payee, payee_cm, ciphertext = paid(BOB.owner_pk, n.open_channel(BOB.address()), 3 * ETH)
    change, change_cm, _ = paid(CAROL.owner_pk, carol_self, ETH)
    chain.add(n.spend_notes(payee, change, ciphertext), [payee_cm, change_cm], [8, 9])
    return chain


def recover(keys, events, **kwargs):
    scanner = n.Scanner(keys, CHAIN, POOL, **kwargs)
    for event in events:
        scanner.scan(event)
    return scanner


def check_primitives():
    checked = 0
    secret = os.urandom(32)
    note, rho = n.seal_note(secret, 7, 123)
    assert len(note) == 48 and n.open_note(secret, 7, note) == 123 and rho == n.note_rho(secret, 7)
    assert n.open_note(secret, 8, note) is None
    assert n.open_note(os.urandom(32), 7, note) is None
    for position in (0, 20, 40, 47):  # the tag, the ciphertext and the authentication tag
        tampered = bytearray(note)
        tampered[position] ^= 1
        assert n.open_note(secret, 7, bytes(tampered)) is None
        checked += 1
    assert len({n.note_tag(secret, i) for i in range(1000)}) == 1000
    for value in (0, w.MAX_VALUE):
        checked += raises(lambda v=value: n.seal_note(secret, 0, v), "positive and fit 128 bits")
    assert all(n.open_note(secret, i, n.dummy_note()) is None for i in range(20))
    checked += raises(lambda: n.spend_notes(note, note[:47]), "two 48-byte notes")
    checked += raises(lambda: n.spend_notes(note, note, b"\x00" * 1000), "two 48-byte notes")
    checked += raises(lambda: n.shield_notes(note + note), "one 48-byte note")
    return checked


def check_keys_and_addresses():
    checked = 0
    again = n.WalletKeys(w.keccak(b"alice"))
    assert again.address() == ALICE.address() and again.spend_key == ALICE.spend_key
    second = n.WalletKeys(w.keccak(b"alice"), account=1)
    assert second.address() != ALICE.address() and second.spend_key != ALICE.spend_key
    assert n.Address.decode(ALICE.address().hex()) == ALICE.address()
    assert len(ALICE.address().encode()) == n.ADDRESS_BYTES == 1217
    checked += raises(lambda: n.WalletKeys(b"\x01" * 31), "at least 32 bytes")
    good = ALICE.address().encode()
    checked += raises(lambda: n.Address.decode(b"\x02" + good[1:]), "starting with version 1")
    checked += raises(lambda: n.Address.decode(good[:-1]), "starting with version 1")
    checked += raises(lambda: n.Address.decode(good[:1] + bytes(32) + good[33:]), "nonzero field element")
    checked += raises(lambda: n.Address.decode(good[:1] + w.P.to_bytes(32, "big") + good[33:]),
                      "nonzero field element")
    # ML-KEM's encapsulation key encodes coefficients below 3329; 0xff bytes are not.
    checked += raises(lambda: n.Address.decode(good[:33] + b"\xff" * 1152 + good[-32:]), "ML-KEM-768 key is invalid")
    checked += raises(lambda: n.Address.decode("0xzz"), "an address is hex")
    checked += raises(lambda: n.direct_channel(ALICE.owner_pk, b"short"), "32 bytes")
    return checked


def check_recovery():
    chain = story()
    alice, bob, carol = (recover(k, chain.events) for k in (ALICE, BOB, CAROL))
    assert Counter(r["value"] for r in alice.notes.values()) == Counter(
        [ETH, ETH // 2, ETH // 5, 2 * ETH, ETH // 10])
    assert Counter(r["value"] for r in bob.notes.values()) == Counter(
        [5 * ETH, 4 * ETH - FEE, 3 * ETH, 2 * ETH, ETH, 3 * ETH])
    assert sorted(r["value"] for r in carol.notes.values()) == [ETH // 3, ETH]
    leaves = {(cm, epoch, index) for e in chain.events for cm, epoch, index in e.leaves}
    found = [*alice.notes.values(), *bob.notes.values(), *carol.notes.values()]
    assert {(int(r["cm"], 16), r["epoch"], r["index"]) for r in found} == leaves, "every leaf has one owner"
    # Bob's deposit was spent by his first payment; the scanner saw its nullifier.
    assert [r["value"] for r in bob.notes.values() if r["spent"]] == [5 * ETH]
    assert len(bob.unspent()) == 5 and len(alice.unspent()) == 5
    # Each note's nullifier is the circuit's, for a later spend.
    for keys, scanner in ((ALICE, alice), (BOB, bob)):
        for r in scanner.notes.values():
            assert int(r["nullifier"], 16) == nullifier_of(keys, int(r["cm"], 16), r["index"])

    # A direct secret past the gap stays hidden until the wallet looks further.
    near = recover(ALICE, chain.events, gap=3)
    assert ETH // 5 not in [r["value"] for r in near.notes.values()] and len(near.notes) == len(alice.notes) - 1

    # Scanning in two runs, through the saved state, finds the same notes.
    first = recover(ALICE, chain.events[:3])
    resumed = n.Scanner.from_json(ALICE, json.loads(json.dumps(first.to_json())))
    for event in chain.events[3:]:
        resumed.scan(event)
    assert resumed.to_json()["notes"] == alice.to_json()["notes"]
    checked = 4
    checked += raises(lambda: n.Scanner.from_json(BOB, alice.to_json()), "another wallet")

    # A node that drops a transaction's logs is caught by the next leaf's index.
    checked += raises(lambda: recover(ALICE, chain.events[:2] + chain.events[3:]), "missing pool logs")
    checked += raises(lambda: recover(ALICE, [chain.events[0], chain.events[1], chain.events[0]]), "chain order")
    return checked


def call_logs(event):
    """One call's logs as the pool emits them: settlement's nullifiers, its leaves, then Notes."""
    entries = [([n.NOTE_SPENT, hex32(nf)], "0x") for nf in event.spent]
    entries += [([n.LEAF_APPENDED, hex32(cm), hex32(epoch)], "0x" + index.to_bytes(32, "big").hex() + "00" * 32)
                for cm, epoch, index in event.leaves]
    body = event.notes + bytes(-len(event.notes) % 32)
    entries.append(([n.NOTES], "0x" + (32).to_bytes(32, "big").hex()
                    + len(event.notes).to_bytes(32, "big").hex() + body.hex()))
    return [{"address": f"0x{POOL:040x}", "topics": topics, "data": data} for topics, data in entries]


def rpc_logs(chain, hidden=()):
    """The chain's events as eth_getLogs results, leaving out the transactions of `hidden` events."""
    left_out = {(chain.events[i].block, chain.events[i].tx) for i in hidden}
    logs, counter = [], Counter()
    for event in chain.events:
        for log in call_logs(event):
            position = counter[event.block]
            counter[event.block] += 1
            if (event.block, event.tx) not in left_out:
                logs.append({**log, "blockNumber": hex(event.block), "transactionIndex": hex(event.tx),
                             "logIndex": hex(position), "transactionHash": f"0x{event.block:032x}{event.tx:032x}"})
    return logs


def rpc_receipts(chain, block, failed=()):
    """A block's receipts. Every transaction is a frame transaction with its pool logs in
    frame 2; for `failed` events, the fourth frame failed."""
    failed_tx = {(chain.events[i].block, chain.events[i].tx) for i in failed}
    receipts = {}
    for event in chain.events:
        if event.block == block:
            receipts.setdefault(event.tx, []).extend(call_logs(event))
    return [{"transactionIndex": hex(tx), "status": "0x0" if (block, tx) in failed_tx else "0x1", "logs": [],
             "frameReceipts": [{"status": "0x1", "logs": []}, {"status": "0x1", "logs": logs}]
             + ([{"status": "0x0", "logs": []}] if (block, tx) in failed_tx else [])}
            for tx, logs in sorted(receipts.items())]


def serve(chain, finalized, hidden=(), unreceipted=()):
    """eth_getLogs leaves out the transactions of `hidden` events, as ethrex does for a
    failed fourth frame; their receipts still show them unless also `unreceipted`."""
    logs = rpc_logs(chain, hidden)
    methods = []
    receipt_chain = Chain()
    receipt_chain.events = [e for i, e in enumerate(chain.events) if i not in unreceipted]

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_POST(self):
            request = json.loads(self.rfile.read(int(self.headers["content-length"])))
            method, params = request["method"], request["params"]
            methods.append(method)
            if method == "eth_chainId":
                result = hex(CHAIN)
            elif method == "eth_getBlockByNumber":
                result = {"number": hex(finalized[0])}
            elif method == "eth_getLogs":
                lo, hi = int(params[0]["fromBlock"], 16), int(params[0]["toBlock"], 16)
                result = [l for l in logs if lo <= int(l["blockNumber"], 16) <= hi]
            elif method == "eth_getBlockReceipts":
                block = int(params[0], 16)
                assert block <= finalized[0]
                result = rpc_receipts(receipt_chain, block, [i for i, e in enumerate(receipt_chain.events)
                                                             if chain.events.index(e) in hidden])
            else:
                result = None
            body = json.dumps({"jsonrpc": "2.0", "id": request["id"], "result": result}).encode()
            self.send_response(200)
            self.send_header("content-type", "application/json")
            self.send_header("content-length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, *args):
            pass

    server = http.server.HTTPServer(("127.0.0.1", 0), Handler)
    server.methods = methods
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server


def write_config(tmp, server, profile=POOL_PROFILE):
    config = Path(tmp, "config.json")
    config.write_text(json.dumps({"chainId": CHAIN, "pool": f"0x{POOL:040x}", "deploymentBlock": 0,
                                  "profile": profile, "rpc": f"http://127.0.0.1:{server.server_port}"}))
    return config


def run_cli(*argv):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        n.main(list(argv))
    return out.getvalue()


def cli_fails(argv, expected):
    try:
        run_cli(*argv)
    except SystemExit as error:
        assert expected in str(error), (expected, str(error))
        return 1
    raise AssertionError(f"the CLI accepted what should fail: {expected}")


def check_cli():
    checked = 0
    chain = story()
    finalized = [chain.events[3].block]
    server = serve(chain, finalized)
    try:
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp, "seed")
            seed.write_text("0x" + w.keccak(b"alice").hex())
            seed.chmod(0o644)
            args = ["--seed-file", str(seed)]
            try:
                run_cli("address", *args)
            except SystemExit as error:
                assert "readable by other users" in str(error)
                checked += 1
            seed.chmod(0o600)
            assert run_cli("address", *args).strip() == ALICE.address().hex()

            state = Path(tmp, "state.json")
            v2 = write_config(tmp, server, "position-notes-v2")
            checked += cli_fails(["scan", "--config", str(v2), "--state", str(state), *args], "publishes notes")
            config = write_config(tmp, server)
            scan = ["scan", "--config", str(config), "--state", str(state), *args]
            direct = ["direct-secret", "--config", str(config), "--state", str(state), *args]
            checked += cli_fails(direct, "scan first")
            first = json.loads(run_cli(*scan))
            assert stat.S_IMODE(state.stat().st_mode) == 0o600
            assert first["scanned_block"] == finalized[0] and first["unspent"] == 3, first
            # Alice's number 3 is paid, so the next number she hands out is 4.
            issued = json.loads(run_cli(*direct))
            assert issued["number"] == 4 and bytes.fromhex(issued["secret"][2:]) == ALICE.direct_secret(4)
            assert json.loads(run_cli(*direct, "--number", "4")) == issued
            checked += cli_fails([*direct, "--number", "5"], "already handed out")
            # Only finalized events count; the next run picks up where this one stopped.
            finalized[0] = chain.events[-1].block
            second = json.loads(run_cli(*scan))
            assert second["unspent"] == 5 and \
                int(second["balance"]) == ETH + ETH // 2 + ETH // 5 + 2 * ETH + ETH // 10, second
            assert json.loads(run_cli(*scan)) == second
            checked += 3
    finally:
        server.shutdown()
    return checked


def check_log_decoding():
    checked = 0
    chain = story()
    assert [(e.key, e.notes, e.leaves, e.spent) for e in n.events_from_logs(rpc_logs(chain))] == \
        [(e.key, e.notes, e.leaves, e.spent) for e in chain.events]
    checked += raises(lambda: n.decode_notes_data("0x" + (64).to_bytes(32, "big").hex() + "00" * 64),
                      "malformed Notes log")
    checked += raises(lambda: n.decode_notes_data("0x" + (32).to_bytes(32, "big").hex()
                                                  + (97).to_bytes(32, "big").hex() + "00" * 97),
                      "malformed Notes log")
    return checked


def check_smoke_fixture():
    """The committed fixture's notes open for its wallets: replaying the story
    as the pool would emit it, each wallet finds and then sees spent its notes."""
    fixture = json.loads((HERE / "fixtures" / "smoke_fixture.json").read_text())
    alice, bob = (n.WalletKeys(bytes.fromhex(fixture["wallets"][name]["seed"][2:])) for name in ("alice", "bob"))
    for name, keys in (("alice", alice), ("bob", bob)):
        assert fixture["wallets"][name]["address"] == keys.address().hex()
    chain_id, pool = fixture["chain_id"], int(fixture["pool_address"], 16)
    t, ws, wd = fixture["transfer"], fixture["withdraw_seed"], fixture["withdraw"]
    hexes = lambda *xs: [int(x, 16) for x in xs]  # noqa: E731
    events = [n.Event(1, bytes.fromhex(fixture["shield_note"][2:]), [(int(fixture["cm_a"], 16), 0, 0)]),
              n.Event(2, bytes.fromhex(t["notes"][2:]), [(int(t["out_cm1"], 16), 0, 1), (int(t["out_cm2"], 16), 0, 2)],
                      hexes(t["nf1"], t["nf2"])),
              n.Event(3, bytes.fromhex(wd["notes"][2:]), [], hexes(wd["nf1"], wd["nf2"])),
              n.Event(4, bytes.fromhex(ws["notes"][2:]), [], hexes(ws["nf1"], ws["nf2"]))]
    found = {}
    for name, keys in (("alice", alice), ("bob", bob)):
        scanner = n.Scanner(keys, chain_id, pool)
        for event in events:
            scanner.scan(event)
        found[name] = sorted((r["index"], r["value"], r["spent"]) for r in scanner.notes.values())
    shield, payment = int(fixture["shield_value"]), int(t["out_value1"])
    change = shield - payment - int(t["fee"])
    assert found == {"alice": [(0, shield, True), (2, change, True)], "bob": [(1, payment, True)]}, found
    return 1


def check_calls_in_one_transaction():
    """A batching contract shields twice in one transaction, and a settlement's fourth
    frame shields: every wallet reads the calls apart instead of stopping."""
    checked = 0
    chain = story()
    note, cm, ciphertext = paid(ALICE.owner_pk, n.open_channel(ALICE.address()), 7 * ETH)
    chain.add(n.shield_notes(note, ciphertext), [cm], sizes=SHIELD_NOTE_BYTES)
    note, cm, _ = paid(BOB.owner_pk, n.direct_channel(BOB.owner_pk, BOB.direct_secret(0)), 6 * ETH)
    chain.add(n.shield_notes(note), [cm], sizes=SHIELD_NOTE_BYTES, same_tx=True)
    carol = recover(CAROL, chain.events)
    paying = next(r for r in carol.notes.values() if r["value"] == ETH and not r["spent"])
    to_alice = n.direct_channel(ALICE.owner_pk, ALICE.direct_secret(0))
    payee, payee_cm, _ = paid(ALICE.owner_pk, to_alice, ETH // 4)
    change, change_cm, _ = paid(CAROL.owner_pk, n.self_channel(carol), ETH // 2)
    chain.add(n.spend_notes(payee, change), [payee_cm, change_cm],
              [int(paying["nullifier"], 16), 12])
    note, cm, _ = paid(ALICE.owner_pk, to_alice, ETH // 8)
    chain.add(n.shield_notes(note), [cm], sizes=SHIELD_NOTE_BYTES, same_tx=True)
    logs = rpc_logs(chain)
    events = n.events_from_logs(logs)
    assert [e.key for e in events] == [e.key for e in chain.events] and events[-1].call == 1
    alice, bob, carol = (recover(k, events) for k in (ALICE, BOB, CAROL))
    assert {7 * ETH, ETH // 4, ETH // 8} <= {r["value"] for r in alice.notes.values()}
    assert 6 * ETH in {r["value"] for r in bob.notes.values()}
    assert {r["value"]: r["spent"] for r in carol.notes.values()} == {ETH // 3: False, ETH: True, ETH // 2: False}
    # A call missing its Notes log, or one of its nullifiers, means the node left logs out.
    last_notes = [l for l in logs if l["topics"][0] == n.NOTES][-1]
    checked += raises(lambda: n.events_from_logs([l for l in logs if l is not last_notes]), "has no Notes log")
    first_spent = next(l for l in logs if l["topics"][0] == n.NOTE_SPENT)
    checked += raises(lambda: n.events_from_logs([l for l in logs if l is not first_spent]), "missing pool logs")
    return checked + 3


def check_channels():
    """A channel's ciphertext goes into one transaction, a sender stays within the
    recipient's window, and payments that land out of order are still found."""
    checked = 0
    channel = n.open_channel(ALICE.address())
    note, rho, index, ciphertext = n.reserve(channel, ETH)
    assert index == 0 and len(ciphertext) == 1088 and channel.ciphertext_sent
    checked += raises(lambda: n.reserve(channel, ETH), "opening payment is not final yet")
    assert n.Outgoing.from_json(json.loads(json.dumps(channel.to_json()))) == channel
    checked += raises(lambda: n.finalized(channel, 1), "never reserved")
    n.finalized(channel, 0)
    assert n.reserve(channel, ETH)[3] == b"" and channel.confirmed == 1

    # A sender keeps fewer than LOOKAHEAD payments past its last final one.
    channel = n.direct_channel(ALICE.owner_pk, ALICE.direct_secret(1))
    notes = [paid(ALICE.owner_pk, channel, ETH + i) for i in range(n.LOOKAHEAD)]
    checked += raises(lambda: n.reserve(channel, ETH), "the recipient watches only")
    n.finalized(channel, 0)
    n.reserve(channel, ETH)
    # Indices 19, 0 and 5 land in that order; a fresh scan finds all three, and so does
    # a scan that saves and reloads its state between them.
    chain = Chain()
    for i in (19, 0, 5):
        chain.add(n.shield_notes(notes[i][0]), [notes[i][1]], sizes=SHIELD_NOTE_BYTES)
    values = {ETH + 19, ETH, ETH + 5}
    assert {r["value"] for r in recover(ALICE, chain.events).notes.values()} == values
    scanner = recover(ALICE, chain.events[:1])
    for event in chain.events[1:]:
        scanner = n.Scanner.from_json(ALICE, json.loads(json.dumps(scanner.to_json())))
        scanner.scan(event)
    assert {r["value"] for r in scanner.notes.values()} == values
    # A later final payment lets the sender run ahead of an older pending one; the
    # older one still lands and is found after a reload.
    channel = n.direct_channel(ALICE.owner_pk, ALICE.direct_secret(2))
    notes = [paid(ALICE.owner_pk, channel, ETH + i) for i in range(n.LOOKAHEAD)]
    n.finalized(channel, n.LOOKAHEAD - 1)
    notes += [paid(ALICE.owner_pk, channel, ETH + i) for i in range(n.LOOKAHEAD, 2 * n.LOOKAHEAD)]
    chain = Chain()
    for i in (n.LOOKAHEAD - 1, 2 * n.LOOKAHEAD - 1, 0):
        chain.add(n.shield_notes(notes[i][0]), [notes[i][1]], sizes=SHIELD_NOTE_BYTES)
    scanner = recover(ALICE, chain.events[:2])
    scanner = n.Scanner.from_json(ALICE, json.loads(json.dumps(scanner.to_json())))
    scanner.scan(chain.events[2])
    assert ETH in {r["value"] for r in scanner.notes.values()}

    # Direct numbers are issued only within GAP of the highest paid one, so a fresh
    # scan watches each before its payment lands, in whatever order they pay.
    scanner = n.Scanner(ALICE, CHAIN, POOL)
    assert [scanner.issue_direct() for _ in range(n.GAP)] == list(range(n.GAP))
    checked += raises(scanner.issue_direct, "waiting for a first payment")
    chain = Chain()
    for number, value in ((19, ETH), (39, 2 * ETH), (25, 3 * ETH), (3, 4 * ETH)):
        if number == 39:
            assert [scanner.issue_direct() for _ in range(n.GAP)][-1] == 39
        note, cm, _ = paid(ALICE.owner_pk, n.direct_channel(ALICE.owner_pk, ALICE.direct_secret(number)), value)
        chain.add(n.shield_notes(note), [cm], sizes=SHIELD_NOTE_BYTES)
        scanner.scan(chain.events[-1])
    assert sorted(r["value"] for r in recover(ALICE, chain.events).notes.values()) == [ETH, 2 * ETH, 3 * ETH, 4 * ETH]
    return checked + 4


def check_restored_self_channel():
    """A restored wallet resumes its change past the indices it may have used."""
    chain = story()
    bob = recover(BOB, chain.events)
    found = next(i for i in bob.incoming if i.kind == "self").next_index
    restored = n.self_channel(bob)
    used = {n.note_tag(BOB.self_secret, i) for i in range(found)}
    change, change_cm, _ = paid(BOB.owner_pk, restored, ETH // 7)
    assert restored.next_index == found + n.RESTORE_SKIP + 1 and change[:16] not in used
    chain.add(n.spend_notes(n.dummy_note(), change), [change_cm], [20, 21])
    assert ETH // 7 in {r["value"] for r in recover(BOB, chain.events).notes.values()}
    for _ in range(n.LOOKAHEAD - n.RESTORE_SKIP - 1):
        n.reserve(restored, 1)
    raises(lambda: n.reserve(restored, 1), "the recipient watches only")
    return 3


def check_hidden_calls():
    """ethrex leaves out of eth_getLogs every log of a transaction whose fourth frame
    failed, settlement included. Once a later leaf shows the gap, the scan rebuilds
    those calls from receipts, in the same run or a later one and whichever node the
    later one uses; a call missing from the receipts too still stops it. The scan
    never asks the node about single nullifiers."""
    checked = 0
    chain = story()
    # Alice spends her direct payment in full: a settlement with no leaf. Left out of
    # the logs, it leaves no gap, so her note still shows as unspent.
    direct_payment = chain.events[3].leaves[0]
    spend = nullifier_of(ALICE, direct_payment[0], direct_payment[2])
    chain.add(n.spend_notes(n.dummy_note(), n.dummy_note()), [], [spend, 13])
    note, cm, _ = paid(BOB.owner_pk, n.direct_channel(BOB.owner_pk, BOB.self_secret), ETH)
    chain.add(n.shield_notes(note), [cm], sizes=SHIELD_NOTE_BYTES)
    alice_notes = {ETH: False, ETH // 2: False, ETH // 5: False, 2 * ETH: False, ETH // 10: False}

    def shields(same_block):
        built = Chain()
        to_alice = n.direct_channel(ALICE.owner_pk, ALICE.direct_secret(0))
        for i in range(5):
            note, cm, _ = paid(ALICE.owner_pk, to_alice, ETH + i)
            built.add(n.shield_notes(note), [cm], sizes=SHIELD_NOTE_BYTES, same_block=i == same_block,
                      skip=5 if i == 3 else 0)
        return built

    fives = {ETH + i: False for i in range(5)}
    # (chain, hidden, unreceipted, [(finalized event, blocks past it, hidden in this run)], outcome)
    cases = [
        (chain, (2, len(chain.events) - 2), (), [(-1, 0, True)], alice_notes),
        (chain, (2,), (2,), [(-1, 0, True)], "missing pool logs"),
        # The second sweep reaches back into the block of a call the first rebuilt.
        (shields(2), (1, 3), (), [(-1, 0, True)], fives),
        # A hidden call in the block of the event that shows the gap, after it.
        (shields(3), (1, 3), (), [(-1, 0, True)], fives),
        # The hidden call is the newest leaf when the first scan runs, which ends
        # blocks after it; a later leaf shows the gap in the next scan, through the
        # same node or an honest one.
        (shields(None), (2,), (), [(2, 3, True), (-1, 0, True)], fives),
        (shields(None), (2,), (), [(2, 3, True), (-1, 0, False)], fives),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        seed = Path(tmp, "seed")
        seed.write_text("0x" + w.keccak(b"alice").hex())
        seed.chmod(0o600)
        for number, (case_chain, hidden, unreceipted, runs, outcome) in enumerate(cases):
            state = Path(tmp, f"state-{number}.json")
            for last, past, hide in runs:
                finalized = [case_chain.events[last].block + past]
                server = serve(case_chain, finalized, hidden if hide else (), unreceipted)
                try:
                    scan = ["scan", "--config", str(write_config(tmp, server)), "--state", str(state),
                            "--seed-file", str(seed)]
                    if isinstance(outcome, str):
                        checked += cli_fails(scan, outcome)
                    else:
                        run_cli(*scan)
                    assert "eth_getStorageAt" not in server.methods
                finally:
                    server.shutdown()
            if not isinstance(outcome, str):
                notes = json.loads(read(state))["notes"]
                assert {r["value"]: r["spent"] for r in notes} == outcome, (number, notes)
                checked += 1
    return checked


def read(path):
    return Path(path).read_text()


def main():
    checked = (check_primitives() + check_keys_and_addresses() + check_recovery() + check_log_decoding()
               + check_calls_in_one_transaction() + check_channels() + check_restored_self_channel()
               + check_hidden_calls() + check_cli() + check_smoke_fixture())
    print(json.dumps({"checks": checked, "spend_notes_bytes": list(SPEND_NOTES_BYTES),
                      "shield_note_bytes": list(SHIELD_NOTE_BYTES), "address_bytes": n.ADDRESS_BYTES},
                     sort_keys=True))


if __name__ == "__main__":
    main()
