#!/usr/bin/env python3
"""Note delivery: wallets find their notes and spends from their seed alone,
through a public address or a secret sent out of band, notes open for no one
else, a node that hides logs is caught, and secrets stay in owner-only files.
The chain is an in-memory list of what the pool emits, and the CLI runs
against a local JSON-RPC server serving the same logs.
Run: python3 wallet/test_notes.py."""
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
sys.path.insert(0, str(HERE))
import notes as n  # noqa: E402
import wallet as w  # noqa: E402
from gas_profile import SHIELD_NOTE_BYTES, SPEND_NOTES_BYTES  # noqa: E402
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
    """The pool's events, one per transaction, and the leaves of epoch 0."""

    def __init__(self):
        self.events, self.size, self.block = [], 0, 100

    def add(self, notes, outputs, spent=(), sizes=SPEND_NOTES_BYTES):
        assert len(notes) in sizes, len(notes)
        leaves = []
        for cm in outputs:
            leaves.append((cm, 0, self.size))
            self.size += 1
        self.block += 1
        self.events.append(n.Event(self.block, notes, leaves, list(spent)))
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

    # The ciphertext stays with the channel until the sender sees it final.
    n.opened(to_alice)
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

    # Carol's first payment to Alice never lands; her retry carries the same
    # ciphertext with the next index, since index 0 is spent from her state.
    to_alice_retry = n.open_channel(ALICE.address())
    n.reserve(to_alice_retry, ETH // 10)
    payee, payee_cm, ciphertext = paid(ALICE.owner_pk, to_alice_retry, ETH // 10)
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


def rpc_logs(chain):
    """The chain's events as eth_getLogs results."""
    logs = []
    for tx, event in enumerate(chain.events):
        entries = [([n.LEAF_APPENDED, hex32(cm), hex32(epoch)], "0x" + index.to_bytes(32, "big").hex() + "00" * 32)
                   for cm, epoch, index in event.leaves]
        entries += [([n.NOTE_SPENT, hex32(nf)], "0x") for nf in event.spent]
        body = event.notes + bytes(-len(event.notes) % 32)
        entries.append(([n.NOTES], "0x" + (32).to_bytes(32, "big").hex()
                        + len(event.notes).to_bytes(32, "big").hex() + body.hex()))
        for log_index, (topics, data) in enumerate(entries):
            logs.append({"address": f"0x{POOL:040x}", "topics": topics, "data": data,
                         "blockNumber": hex(event.block), "transactionIndex": hex(tx % 3),
                         "logIndex": hex(log_index), "transactionHash": f"0x{tx:064x}"})
    return logs


def serve(chain, finalized):
    logs = rpc_logs(chain)

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_POST(self):
            request = json.loads(self.rfile.read(int(self.headers["content-length"])))
            method, params = request["method"], request["params"]
            if method == "eth_chainId":
                result = hex(CHAIN)
            elif method == "eth_getBlockByNumber":
                result = {"number": hex(finalized[0])}
            elif method == "eth_getLogs":
                lo, hi = int(params[0]["fromBlock"], 16), int(params[0]["toBlock"], 16)
                result = [l for l in logs if lo <= int(l["blockNumber"], 16) <= hi]
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
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server


def run_cli(*argv):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        n.main(list(argv))
    return out.getvalue()


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
            direct = json.loads(run_cli("direct-secret", "--number", "3", *args))
            assert bytes.fromhex(direct["secret"][2:]) == ALICE.direct_secret(3)

            config = Path(tmp, "config.json")
            config.write_text(json.dumps({"chainId": CHAIN, "pool": f"0x{POOL:040x}", "deploymentBlock": 0,
                                          "rpc": f"http://127.0.0.1:{server.server_port}"}))
            state = Path(tmp, "state.json")
            scan = ["scan", "--config", str(config), "--state", str(state), *args]
            first = json.loads(run_cli(*scan))
            assert stat.S_IMODE(state.stat().st_mode) == 0o600
            assert first["scanned_block"] == finalized[0] and first["unspent"] == 3, first
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
    assert [(e.notes, e.leaves, e.spent) for e in n.events_from_logs(rpc_logs(chain))] == \
        [(e.notes, e.leaves, e.spent) for e in chain.events]
    checked += raises(lambda: n.decode_notes_data("0x" + (64).to_bytes(32, "big").hex() + "00" * 64),
                      "malformed Notes log")
    checked += raises(lambda: n.decode_notes_data("0x" + (32).to_bytes(32, "big").hex()
                                                  + (97).to_bytes(32, "big").hex() + "00" * 97),
                      "malformed Notes log")
    return checked


def check_smoke_fixture():
    """The committed fixture's notes open for its wallets: replaying the story
    as the pool would emit it, each wallet finds and then sees spent its notes."""
    fixture = json.loads((HERE / "smoke_fixture.json").read_text())
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


def main():
    checked = (check_primitives() + check_keys_and_addresses() + check_recovery() + check_log_decoding()
               + check_cli() + check_smoke_fixture())
    print(json.dumps({"checks": checked, "spend_notes_bytes": list(SPEND_NOTES_BYTES),
                      "shield_note_bytes": list(SHIELD_NOTE_BYTES), "address_bytes": n.ADDRESS_BYTES},
                     sort_keys=True))


if __name__ == "__main__":
    main()
