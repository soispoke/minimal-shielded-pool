"""Note delivery: one secret per sender and recipient, and 48-byte notes.

The pool publishes notes and never reads them (contracts/src/ShieldedPoolLogic.sol).
Settlement calldata is settle(Spend) followed by two notes, one per output, and a
shield carries one. A sender's first payment to a public address puts its ML-KEM-768
ciphertext before the notes.

  note = tag (16) || ChaCha20-Poly1305(key, value as 16 bytes) (16 + 16)
  tag  = PRF(K, "tag", i)[:16]
  key  = PRF(K, "key", i)             the nonce is zero: each key encrypts one note
  rho  = PRF64(K, "rho", i) mod r      the recipient recomputes the commitment
  cm   = Poseidon(2, Poseidon2(owner_pk, rho), value)

PRF is HMAC-SHA256, and PRF64 joins two outputs into 512 bits before reducing mod r.
`i` counts the notes a sender has sent with `K`. A sender must never reuse an index:
a repeated tag links two payments.

`K`, the secret a sender and recipient share, comes from one of two places:

  * The recipient's public address, owner_pk (32 bytes) || ML-KEM-768 encapsulation
    key (1,184 bytes). The sender encapsulates with randomness derived from its own
    seed, so it can recompute `K` later, and its first payment carries the ciphertext.
    The recipient decapsulates every ciphertext it sees. ML-KEM returns a random key
    for a ciphertext made for someone else, so the payee note's tag at index 0 is what
    confirms a match.
  * A direct secret, PRF(seed, "direct", n), which the recipient sends to the sender
    over a post-quantum channel. Nothing extra goes on chain. The recipient finds its
    direct secrets again by deriving n = 0, 1, 2, ... until GAP in a row are unused.

Change uses PRF(seed, "self"). A withdrawal puts a random dummy in the payee note.

All notes paid to one address share its spend_key. A disclosure receipt reveals
Poseidon2(D, spend_key) (wallet/disclosure.py), which then identifies every spend of
that address in epoch D, not only the disclosed note. A wallet that issues receipts
should give each counterparty its own address (`account`).

kyber-py is a pure-Python ML-KEM that is not constant time. It suits this research
wallet, not production keys.
"""
import hashlib
import hmac
import os
import sys
from pathlib import Path

from Crypto.Cipher import ChaCha20_Poly1305
from kyber_py.ml_kem import ML_KEM_768

sys.path.insert(0, str(Path(__file__).parent.parent / "devnet"))
sys.path.insert(0, str(Path(__file__).parent))
from gas_profile import KEM_CIPHERTEXT_BYTES, NOTE_BYTES  # noqa: E402
from wallet import TAG_LEAF, P, commitment, owner_pk, p2, tagged  # noqa: E402

LABEL = b"minimal-shielded-pool:note:v1:"
TAG_BYTES = 16
VALUE_BYTES = 16
MAC_BYTES = 16
EK_BYTES = 1184
ADDRESS_BYTES = 32 + EK_BYTES
GAP = 20
LOOKAHEAD = 20
assert TAG_BYTES + VALUE_BYTES + MAC_BYTES == NOTE_BYTES


def _encode(part):
    if isinstance(part, int):
        return part.to_bytes(32, "big")
    return bytes(part)


def prf(key, label, *parts):
    """HMAC-SHA256 under a domain-separated label."""
    message = LABEL + label.encode() + b"".join(b"|" + _encode(p) for p in parts)
    return hmac.new(key, message, hashlib.sha256).digest()


def prf_field(key, label, *parts):
    """A field element from 512 PRF bits, so the reduction mod r has no useful bias."""
    wide = prf(key, label + ":0", *parts) + prf(key, label + ":1", *parts)
    return int.from_bytes(wide, "big") % P


def note_tag(secret, index):
    return prf(secret, "tag", index)[:TAG_BYTES]


def note_rho(secret, index):
    return prf_field(secret, "rho", index)


def make_note(secret, index, value):
    """The 48-byte note for the index-th payment under `secret`, and its rho."""
    if not 0 <= value < 1 << 128:
        raise ValueError("value must fit 128 bits")
    tag = note_tag(secret, index)
    cipher = ChaCha20_Poly1305.new(key=prf(secret, "key", index), nonce=bytes(12))
    cipher.update(tag)
    encrypted, mac = cipher.encrypt_and_digest(value.to_bytes(VALUE_BYTES, "big"))
    return tag + encrypted + mac, note_rho(secret, index)


def open_note(secret, index, note):
    """The note's value, or None if it was not made with (secret, index)."""
    if len(note) != NOTE_BYTES or note[:TAG_BYTES] != note_tag(secret, index):
        return None
    cipher = ChaCha20_Poly1305.new(key=prf(secret, "key", index), nonce=bytes(12))
    cipher.update(note[:TAG_BYTES])
    try:
        value = cipher.decrypt_and_verify(note[TAG_BYTES:TAG_BYTES + VALUE_BYTES],
                                          note[TAG_BYTES + VALUE_BYTES:])
    except ValueError:
        return None
    return int.from_bytes(value, "big")


def dummy_note():
    """Random bytes in a note's place: a withdrawal's payee note opens for no one."""
    return os.urandom(NOTE_BYTES)


class Keys:
    """A wallet's keys for one address, all derived from its seed."""

    def __init__(self, seed, account=0):
        self.root = prf(seed, "account", account)
        self.spend_key = prf_field(self.root, "spend")
        if self.spend_key == 0:
            raise ValueError("degenerate spend key")
        self.owner_pk = owner_pk(self.spend_key)
        self.ek, self.dk = ML_KEM_768._keygen_internal(prf(self.root, "kem-d"), prf(self.root, "kem-z"))
        self.self_secret = prf(self.root, "self")
        self.seed = seed

    def address(self):
        """The public address: owner_pk, then the ML-KEM-768 encapsulation key."""
        return self.owner_pk.to_bytes(32, "big") + self.ek

    def direct_secret(self, n):
        """The n-th secret this wallet hands to a sender over a post-quantum channel."""
        return prf(self.root, "direct", n)


def parse_address(address):
    if len(address) != ADDRESS_BYTES:
        raise ValueError(f"an address is {ADDRESS_BYTES} bytes")
    return int.from_bytes(address[:32], "big"), address[32:]


def first_payment(sender_seed, address, channel=0):
    """The shared secret and ML-KEM ciphertext for paying a public address.

    The encapsulation randomness comes from the sender's seed, so the sender can recompute
    both later. `channel` opens another, unlinkable secret with the same recipient.
    """
    _, ek = parse_address(address)
    randomness = prf(sender_seed, "encaps", hashlib.sha256(ek).digest(), channel)
    secret, ciphertext = ML_KEM_768._encaps_internal(ek, randomness)
    assert len(ciphertext) == KEM_CIPHERTEXT_BYTES
    return secret, ciphertext


def output_commitment(recipient_owner_pk, rho, value):
    """cm for an output paid to `recipient_owner_pk` (wallet.commitment takes a spend_key)."""
    return tagged(TAG_LEAF, p2(recipient_owner_pk, rho), value)


def spend_notes(payee_note, change_note, ciphertext=b""):
    """Settlement's notes: an optional ciphertext, then the payee and change notes."""
    if len(payee_note) != NOTE_BYTES or len(change_note) != NOTE_BYTES:
        raise ValueError("each note is 48 bytes")
    if ciphertext and len(ciphertext) != KEM_CIPHERTEXT_BYTES:
        raise ValueError("a ciphertext is 1,088 bytes")
    return ciphertext + payee_note + change_note


def shield_note(note, ciphertext=b""):
    """A shield's note, optionally after a ciphertext."""
    if len(note) != NOTE_BYTES:
        raise ValueError("a note is 48 bytes")
    if ciphertext and len(ciphertext) != KEM_CIPHERTEXT_BYTES:
        raise ValueError("a ciphertext is 1,088 bytes")
    return ciphertext + note


class Scanner:
    """Finds a wallet's notes in the pool's events, from its seed alone.

    Each event is the notes one shield or settlement published, with the leaves it
    appended as (cm, epoch, index). The scanner keeps the next LOOKAHEAD tags of every
    secret it knows and decapsulates every ciphertext.
    """

    def __init__(self, keys, gap=GAP, lookahead=LOOKAHEAD):
        self.keys = keys
        self.gap = gap
        self.lookahead = lookahead
        self.tags = {}
        self.next_index = {}
        self.direct_used = -1
        self.found = []
        self._watch(keys.self_secret, 0)
        for n in range(gap):
            self._watch(keys.direct_secret(n), 0, direct=n)

    def _watch(self, secret, start, direct=None):
        for index in range(start, start + self.lookahead):
            self.tags[note_tag(secret, index)] = (secret, index, direct)

    def _take(self, secret, index, direct, note, leaves):
        value = open_note(secret, index, note)
        if value is None:
            return
        rho = note_rho(secret, index)
        cm = commitment(self.keys.spend_key, rho, value)
        for leaf_cm, epoch, leaf in leaves:
            if leaf_cm == cm:
                self.found.append({"value": value, "rho": rho, "spend_key": self.keys.spend_key,
                                   "cm": cm, "epoch": epoch, "index": leaf})
                break
        else:
            return
        if index + 1 >= self.next_index.get(secret, 0):
            self.next_index[secret] = index + 1
            self._watch(secret, index + 1)
        if direct is not None and direct > self.direct_used:
            for n in range(self.direct_used + self.gap + 1, direct + self.gap + 1):
                self._watch(self.keys.direct_secret(n), 0, direct=n)
            self.direct_used = direct

    def scan(self, notes, leaves):
        """Process one event's notes and leaves; return the notes this wallet received."""
        before = len(self.found)
        body = notes
        # One or two notes, or a ciphertext first: a first payment to a public address.
        if len(notes) > 2 * NOTE_BYTES:
            ciphertext, body = notes[:KEM_CIPHERTEXT_BYTES], notes[KEM_CIPHERTEXT_BYTES:]
            secret = ML_KEM_768.decaps(self.keys.dk, ciphertext)
            for offset in range(0, len(body), NOTE_BYTES):
                if body[offset:offset + TAG_BYTES] == note_tag(secret, 0):
                    self._watch(secret, 0)
                    break
        for offset in range(0, len(body), NOTE_BYTES):
            note = body[offset:offset + NOTE_BYTES]
            match = self.tags.get(note[:TAG_BYTES])
            if match is not None:
                self._take(*match, note, leaves)
        return self.found[before:]
