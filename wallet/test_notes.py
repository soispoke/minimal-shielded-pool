#!/usr/bin/env python3
"""Notes let a wallet find its payments from its seed alone, through a public address
or a direct secret, and they open for no one else. The chain here is what the pool
emits: each shield's or settlement's notes, with the leaves that event appended.
Run: python3 wallet/test_notes.py."""
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import notes as n  # noqa: E402
from gas_profile import SHIELD_NOTE_BYTES, SPEND_NOTES_BYTES  # noqa: E402

ETH = 10**18
FEE = ETH // 100


class Pool:
    """The append-only tree as events: notes, and the leaves each event appended."""

    def __init__(self):
        self.events, self.size = [], 0

    def add(self, notes, commitments, sizes):
        assert len(notes) in sizes, len(notes)
        leaves = []
        for cm in commitments:
            leaves.append((cm, 0, self.size))
            self.size += 1
        self.events.append((notes, leaves))


def recover(keys, gap=n.GAP):
    scanner = n.Scanner(keys, gap=gap)
    for notes, leaves in POOL.events:
        scanner.scan(notes, leaves)
    return scanner.found


def output(keys_or_owner, secret, index, value):
    """A note for `value` and the commitment it opens to."""
    note, rho = n.make_note(secret, index, value)
    owner = keys_or_owner if isinstance(keys_or_owner, int) else keys_or_owner.owner_pk
    return note, n.output_commitment(owner, rho, value)


POOL = Pool()
ALICE, BOB, CAROL = (n.Keys(seed) for seed in (b"alice seed", b"bob seed", b"carol seed"))


def story():
    """Bob shields, pays Alice four ways and withdraws; Carol pays Bob once."""
    alice_owner = n.parse_address(ALICE.address())[0]
    bob_owner = n.parse_address(BOB.address())[0]

    note, cm = output(BOB, BOB.self_secret, 0, 5 * ETH)
    POOL.add(n.shield_note(note), [cm], SHIELD_NOTE_BYTES)

    # First payment to Alice's public address: the ciphertext sets up the secret.
    secret, ciphertext = n.first_payment(BOB.seed, ALICE.address())
    payee, payee_cm = output(alice_owner, secret, 0, ETH)
    change, change_cm = output(BOB, BOB.self_secret, 1, 4 * ETH - FEE)
    POOL.add(n.spend_notes(payee, change, ciphertext), [payee_cm, change_cm], SPEND_NOTES_BYTES)

    # A later payment on the same secret carries no ciphertext.
    payee, payee_cm = output(alice_owner, secret, 1, ETH // 2)
    change, change_cm = output(BOB, BOB.self_secret, 2, 4 * ETH - ETH // 2 - 2 * FEE)
    POOL.add(n.spend_notes(payee, change), [change_cm, payee_cm], SPEND_NOTES_BYTES)

    # Alice handed Bob her direct secret number 3 over Signal: nothing extra on chain.
    payee, payee_cm = output(alice_owner, ALICE.direct_secret(3), 0, ETH // 5)
    change, change_cm = output(BOB, BOB.self_secret, 3, 4 * ETH - ETH // 2 - ETH // 5 - 3 * FEE)
    POOL.add(n.spend_notes(payee, change), [payee_cm, change_cm], SPEND_NOTES_BYTES)

    # A withdrawal: the payee note is a dummy and only the change is a leaf.
    change, change_cm = output(BOB, BOB.self_secret, 4, ETH)
    POOL.add(n.spend_notes(n.dummy_note(), change), [change_cm], SPEND_NOTES_BYTES)

    # A shield straight to Alice's public address, on a second, unlinkable secret.
    secret2, ciphertext2 = n.first_payment(BOB.seed, ALICE.address(), channel=1)
    note, cm = output(alice_owner, secret2, 0, 2 * ETH)
    POOL.add(n.shield_note(note, ciphertext2), [cm], SHIELD_NOTE_BYTES)

    # Carol pays Bob's public address. Alice decapsulates this ciphertext too.
    secret3, ciphertext3 = n.first_payment(CAROL.seed, BOB.address())
    payee, payee_cm = output(bob_owner, secret3, 0, 3 * ETH)
    change, change_cm = output(CAROL, CAROL.self_secret, 0, ETH)
    POOL.add(n.spend_notes(payee, change, ciphertext3), [payee_cm, change_cm], SPEND_NOTES_BYTES)
    return secret, ciphertext


def main():
    secret, ciphertext = story()

    alice = recover(ALICE)
    assert Counter(f["value"] for f in alice) == Counter([ETH, ETH // 2, ETH // 5, 2 * ETH]), alice
    bob = recover(BOB)
    assert Counter(f["value"] for f in bob) == Counter(
        [5 * ETH, 4 * ETH - FEE, 4 * ETH - ETH // 2 - 2 * FEE,
         4 * ETH - ETH // 2 - ETH // 5 - 3 * FEE, ETH, 3 * ETH]), bob
    carol = recover(CAROL)
    assert [f["value"] for f in carol] == [ETH], carol

    # Every note found is a leaf the wallet can spend: its commitment and position.
    leaves = {(cm, epoch, index) for _, ls in POOL.events for cm, epoch, index in ls}
    for wallet, found in ((ALICE, alice), (BOB, bob), (CAROL, carol)):
        for f in found:
            assert (f["cm"], f["epoch"], f["index"]) in leaves
            assert f["spend_key"] == wallet.spend_key
    assert len({f["index"] for f in alice + bob + carol}) == len(alice + bob + carol) == POOL.size

    # The sender recomputes its secret and ciphertext from its seed, to resume the index.
    assert n.first_payment(BOB.seed, ALICE.address()) == (secret, ciphertext)
    assert n.first_payment(BOB.seed, ALICE.address(), channel=1)[1] != ciphertext

    # A note opens only under its own secret and index, and tags never repeat.
    note, _ = n.make_note(secret, 7, 123)
    assert n.open_note(secret, 7, note) == 123
    assert n.open_note(secret, 8, note) is None
    assert n.open_note(BOB.self_secret, 7, note) is None
    tampered = note[:20] + bytes([note[20] ^ 1]) + note[21:]
    assert n.open_note(secret, 7, tampered) is None
    assert len({n.note_tag(secret, i) for i in range(1000)}) == 1000

    # A direct secret past the gap stays hidden until the wallet looks further.
    near = recover(ALICE, gap=3)
    assert ETH // 5 not in [f["value"] for f in near], near
    assert len(near) == len(alice) - 1

    print(json.dumps({"alice_found": len(alice), "bob_found": len(bob), "carol_found": len(carol),
                      "events": len(POOL.events), "leaves": POOL.size,
                      "spend_notes_bytes": list(SPEND_NOTES_BYTES),
                      "shield_note_bytes": list(SHIELD_NOTE_BYTES),
                      "address_bytes": len(ALICE.address())}, sort_keys=True))


if __name__ == "__main__":
    main()
