#!/usr/bin/env python3
"""Note delivery: a secret per sender and recipient, and 48-byte notes on chain.

A recipient needs each note's amount and rho to spend it. The pool publishes
notes and never reads them (contracts/src/ShieldedPoolLogic.sol): settlement
carries two notes, one per output, and a shield carries one. A sender's first
payment to a public address puts its ML-KEM-768 ciphertext before the notes.

  note = tag (16) || ChaCha20-Poly1305(value as 16 bytes) (16 + 16 tag)
  tag  = PRF(K, "tag", i)[:16]
  key  = PRF(K, "key", i)              each key seals one note, so the nonce is zero
  rho  = PRF64(K, "rho", i) mod r       the recipient recomputes the commitment
  cm   = Poseidon(2, Poseidon2(owner_pk, rho), value)

PRF is HMAC-SHA256 and PRF64 joins two outputs into 512 bits before reducing.
`i` counts the notes sent under K. Reusing an index repeats a tag, which links
two payments, so a sender reserves each index in its saved state before using it.

K, the secret a sender and recipient share, comes from one of two places:

  * The recipient's public address: a version byte, owner_pk and an ML-KEM-768
    encapsulation key (1,217 bytes). The sender encapsulates, and its first
    payment carries the 1,088-byte ciphertext. The recipient decapsulates every
    ciphertext. ML-KEM returns a pseudorandom key for a ciphertext made for
    someone else, so a note tag at one of the first LOOKAHEAD indices confirms
    a match. That covers a retry after a first payment that never landed.
  * Out of band: the recipient derives K = PRF(root, "direct", n) and sends it
    to the sender over a post-quantum channel. Nothing extra goes on chain. The
    recipient finds these again by deriving n = 0, 1, 2, ... until GAP in a row
    are unused.

Change and shields from one's own funds use K = PRF(root, "self"). A withdrawal
puts a random dummy in the payee note.

Recovery: a recipient rebuilds every incoming note, and every change note, from
its seed alone. A sender cannot recompute an outgoing secret it encapsulated
(the randomness is the library's), so after a restore it opens a new one with
each recipient; its funds are its change notes and come back from the seed.

All notes paid to one address share its spend key. A disclosure receipt for one
of them reveals Poseidon2(D, spend_key), which identifies every spend of that
address in epoch D, so wallet/disclosure.py refuses such a receipt unless asked
for it explicitly.

  notes.py address [--account N] [--seed-file PATH]
  notes.py direct-secret --number N [--account N] [--seed-file PATH]
  notes.py scan --config CONFIG --state PATH [--rpc URL] [--account N] [--seed-file PATH]

Without --seed-file the seed is read from the terminal, or from standard input,
never from the command line.
"""
import argparse
import getpass
import hashlib
import hmac
import json
import os
import stat
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.asymmetric.mlkem import MLKEM768PrivateKey, MLKEM768PublicKey
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "devnet"))
import wallet as w  # noqa: E402
from gas_profile import KEM_CIPHERTEXT_BYTES, NOTE_BYTES, SHIELD_NOTE_BYTES, SPEND_NOTES_BYTES  # noqa: E402
from poseidon_bn254 import hex32  # noqa: E402

LABEL = b"minimal-shielded-pool:note:v1:"
TAG_BYTES = 16
VALUE_BYTES = 16
SECRET_BYTES = 32
EK_BYTES = 1184
ADDRESS_VERSION = 1
ADDRESS_BYTES = 1 + 32 + EK_BYTES
MIN_SEED_BYTES = 32
GAP = 20
LOOKAHEAD = 20
STATE_VERSION = 1
assert TAG_BYTES + VALUE_BYTES + 16 == NOTE_BYTES


class NotesError(Exception):
    """Invalid input, an inconsistent chain view, or a state file that cannot be trusted."""


# ---- primitives ----

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
    return int.from_bytes(wide, "big") % w.P


def note_tag(secret, index):
    return prf(secret, "tag", index)[:TAG_BYTES]


def note_rho(secret, index):
    return prf_field(secret, "rho", index)


def seal_note(secret, index, value):
    """The 48-byte note for the index-th payment under `secret`, and its rho."""
    if not 0 < value < w.MAX_VALUE:
        raise NotesError("a note's value must be positive and fit 128 bits")
    tag = note_tag(secret, index)
    sealed = ChaCha20Poly1305(prf(secret, "key", index)).encrypt(
        bytes(12), value.to_bytes(VALUE_BYTES, "big"), tag)
    return tag + sealed, note_rho(secret, index)


def open_note(secret, index, note):
    """The note's value, or None if it was not sealed with (secret, index)."""
    if len(note) != NOTE_BYTES or not hmac.compare_digest(note[:TAG_BYTES], note_tag(secret, index)):
        return None
    try:
        plain = ChaCha20Poly1305(prf(secret, "key", index)).decrypt(bytes(12), note[TAG_BYTES:],
                                                                     note[:TAG_BYTES])
    except InvalidTag:
        return None
    value = int.from_bytes(plain, "big")
    return value if 0 < value < w.MAX_VALUE else None


def dummy_note():
    """Random bytes in a note's place, for a withdrawal's payee: they open for no one."""
    return os.urandom(NOTE_BYTES)


def spend_notes(payee_note, change_note, ciphertext=b""):
    """Settlement's notes: an optional ciphertext, then the payee and change notes."""
    data = bytes(ciphertext) + bytes(payee_note) + bytes(change_note)
    if len(payee_note) != NOTE_BYTES or len(change_note) != NOTE_BYTES or len(data) not in SPEND_NOTES_BYTES:
        raise NotesError("a spend carries two 48-byte notes, optionally after a 1,088-byte ciphertext")
    return data


def shield_notes(note, ciphertext=b""):
    """A shield's note, optionally after a ciphertext."""
    data = bytes(ciphertext) + bytes(note)
    if len(note) != NOTE_BYTES or len(data) not in SHIELD_NOTE_BYTES:
        raise NotesError("a shield carries one 48-byte note, optionally after a 1,088-byte ciphertext")
    return data


def output_commitment(owner_pk, rho, value):
    """cm of an output paid to owner_pk (wallet.commitment takes a spend key instead)."""
    return w.tagged(w.TAG_LEAF, w.p2(owner_pk, rho), value)


# ---- keys and addresses ----

@dataclass(frozen=True)
class Address:
    """A public address: owner_pk and an ML-KEM-768 encapsulation key."""
    owner_pk: int
    ek: bytes

    def encode(self):
        return bytes([ADDRESS_VERSION]) + self.owner_pk.to_bytes(32, "big") + self.ek

    def hex(self):
        return "0x" + self.encode().hex()

    @classmethod
    def decode(cls, data):
        if isinstance(data, str):
            try:
                data = bytes.fromhex(data.removeprefix("0x"))
            except ValueError:
                raise NotesError("an address is hex") from None
        if len(data) != ADDRESS_BYTES or data[0] != ADDRESS_VERSION:
            raise NotesError(f"an address is {ADDRESS_BYTES} bytes starting with version {ADDRESS_VERSION}")
        owner_pk = int.from_bytes(data[1:33], "big")
        if not 0 < owner_pk < w.P:
            raise NotesError("the address's owner key is not a nonzero field element")
        try:
            MLKEM768PublicKey.from_public_bytes(data[33:])
        except ValueError:
            raise NotesError("the address's ML-KEM-768 key is invalid") from None
        return cls(owner_pk, bytes(data[33:]))


class WalletKeys:
    """One address's keys, all derived from the wallet seed."""

    def __init__(self, seed, account=0):
        if len(seed) < MIN_SEED_BYTES:
            raise NotesError(f"a seed has at least {MIN_SEED_BYTES} bytes")
        if account < 0:
            raise NotesError("an account number is nonnegative")
        self.account = account
        self.root = prf(seed, "account", account)
        self.spend_key = prf_field(self.root, "spend")
        if self.spend_key == 0:
            raise NotesError("degenerate spend key")
        self.owner_pk = w.owner_pk(self.spend_key)
        # FIPS 203's 64-byte seed (d || z) regenerates the same key pair.
        self.kem = MLKEM768PrivateKey.from_seed_bytes(prf(self.root, "kem-d") + prf(self.root, "kem-z"))
        self.self_secret = prf(self.root, "self")

    def address(self):
        return Address(self.owner_pk, self.kem.public_key().public_bytes_raw())

    def direct_secret(self, number):
        """The secret this wallet hands its number-th out-of-band sender."""
        if number < 0:
            raise NotesError("a direct secret number is nonnegative")
        return prf(self.root, "direct", number)

    def decapsulate(self, ciphertext):
        return self.kem.decapsulate(ciphertext)


# ---- sending ----

@dataclass
class Outgoing:
    """A sender's secret with one recipient, and the next index it may use."""
    owner_pk: int
    secret: bytes
    next_index: int = 0
    ciphertext: bytes = b""  # sent with every payment until one carrying it is final

    def to_json(self):
        return {"owner_pk": hex32(self.owner_pk), "secret": "0x" + self.secret.hex(),
                "next_index": self.next_index, "ciphertext": "0x" + self.ciphertext.hex()}

    @classmethod
    def from_json(cls, data):
        return cls(int(data["owner_pk"], 16), bytes.fromhex(data["secret"][2:]), int(data["next_index"]),
                   bytes.fromhex(data["ciphertext"][2:]))


def open_channel(address):
    """A new secret with the owner of a public address, and the ciphertext that carries it."""
    if isinstance(address, (str, bytes)):
        address = Address.decode(address)
    secret, ciphertext = MLKEM768PublicKey.from_public_bytes(address.ek).encapsulate()
    if len(secret) != SECRET_BYTES or len(ciphertext) != KEM_CIPHERTEXT_BYTES:
        raise NotesError("unexpected ML-KEM-768 output sizes")
    return Outgoing(address.owner_pk, secret, 0, ciphertext)


def direct_channel(owner_pk, secret):
    """The sender's side of a secret the recipient handed over out of band."""
    if len(secret) != SECRET_BYTES or not 0 < owner_pk < w.P:
        raise NotesError("a direct secret is 32 bytes for a nonzero owner key")
    return Outgoing(owner_pk, bytes(secret))


def opened(channel):
    """Stop sending the ciphertext once a payment that carried it is final."""
    channel.ciphertext = b""


def reserve(channel, value):
    """Seal the channel's next note and advance its index.

    Save the wallet state before broadcasting the transaction that carries the
    note: an index used twice repeats its tag. Returns (note, rho, index,
    ciphertext); the ciphertext is empty once the channel is open on chain.
    """
    index = channel.next_index
    note, rho = seal_note(channel.secret, index, value)
    channel.next_index += 1
    return note, rho, index, channel.ciphertext


# ---- receiving ----

@dataclass
class Event:
    """What one shield or settlement published, in chain order."""
    block: int
    notes: bytes
    leaves: list  # (cm, epoch, index), in insertion order
    spent: list = field(default_factory=list)  # nullifiers


@dataclass
class Incoming:
    secret: bytes
    kind: str  # "self", "direct" or "kem"
    next_index: int = 0
    number: int = -1  # the direct secret's number, -1 otherwise


class Scanner:
    """Finds a wallet's notes and their spends in the pool's events, from its seed.

    It reads finalized events only and checks that each epoch's leaves arrive
    without gaps: a node that left a transaction's logs out, or pruned old ones,
    fails loudly instead of hiding a payment.
    """

    def __init__(self, keys, chain_id, pool, gap=GAP, lookahead=LOOKAHEAD):
        self.keys, self.chain_id, self.pool = keys, chain_id, pool
        self.gap, self.lookahead = gap, lookahead
        self.incoming = []
        self.tags = {}
        self.direct_highest = -1
        self.tree = {}  # epoch -> next leaf index
        self.notes = {}  # (epoch, index) -> note record
        self.nullifiers = {}  # nullifier -> (epoch, index)
        self.scanned_block = -1
        self._add(Incoming(keys.self_secret, "self"))
        for number in range(gap):
            self._add(Incoming(keys.direct_secret(number), "direct", number=number))

    def _add(self, incoming):
        self.incoming.append(incoming)
        self._watch(len(self.incoming) - 1)

    def _watch(self, position):
        incoming = self.incoming[position]
        for index in range(incoming.next_index, incoming.next_index + self.lookahead):
            self.tags[note_tag(incoming.secret, index)] = (position, index)

    def _known(self, secret):
        return any(hmac.compare_digest(i.secret, secret) for i in self.incoming)

    def scan(self, event):
        """Apply one event. Returns the notes it paid to this wallet."""
        if event.block < self.scanned_block:
            raise NotesError("events must arrive in chain order")
        for cm, epoch, index in event.leaves:
            expected = self.tree.get(epoch, 0)
            if index != expected:
                raise NotesError(f"leaf {index} of epoch {epoch} arrived where {expected} was expected; "
                                 "this node is missing pool logs, so notes may be hidden")
            self.tree[epoch] = index + 1
        for nullifier in event.spent:
            place = self.nullifiers.get(nullifier)
            if place is not None:
                self.notes[place]["spent"] = True
        body = event.notes
        if len(body) in (KEM_CIPHERTEXT_BYTES + NOTE_BYTES, KEM_CIPHERTEXT_BYTES + 2 * NOTE_BYTES):
            secret = self.keys.decapsulate(body[:KEM_CIPHERTEXT_BYTES])
            body = body[KEM_CIPHERTEXT_BYTES:]
            # A sender whose first payment failed retries with the same ciphertext at a
            # later index, so look for any index in the window, not only 0.
            window = {note_tag(secret, i) for i in range(self.lookahead)}
            if not self._known(secret) and any(body[o:o + TAG_BYTES] in window
                                               for o in range(0, len(body), NOTE_BYTES)):
                self._add(Incoming(secret, "kem"))
        elif len(body) not in (NOTE_BYTES, 2 * NOTE_BYTES, 0):
            raise NotesError(f"an event published {len(body)} note bytes")
        found = []
        for offset in range(0, len(body), NOTE_BYTES):
            note = body[offset:offset + NOTE_BYTES]
            match = self.tags.get(note[:TAG_BYTES])
            if match is not None:
                record = self._take(match, note, event.leaves)
                if record is not None:
                    found.append(record)
        self.scanned_block = max(self.scanned_block, event.block)
        return found

    def _take(self, match, note, leaves):
        position, index = match
        incoming = self.incoming[position]
        value = open_note(incoming.secret, index, note)
        if value is None:
            return None
        rho = note_rho(incoming.secret, index)
        cm = w.commitment(self.keys.spend_key, rho, value)
        place = next(((epoch, leaf) for leaf_cm, epoch, leaf in leaves if leaf_cm == cm), None)
        if place is None or place in self.notes:
            return None  # a note naming no output of its own event pays nobody
        nullifier = w.nullifier(w.domain_scalar(self.chain_id, self.pool, place[0]),
                                self.keys.spend_key, cm, place[1])
        record = {"cm": hex32(cm), "epoch": place[0], "index": place[1], "value": value,
                  "rho": hex32(rho), "nullifier": hex32(nullifier), "spent": False,
                  "secret": incoming.kind}
        self.notes[place] = record
        self.nullifiers[nullifier] = place
        if index + 1 > incoming.next_index:
            incoming.next_index = index + 1
            self._watch(position)
        if incoming.kind == "direct" and incoming.number > self.direct_highest:
            for number in range(self.direct_highest + self.gap + 1, incoming.number + self.gap + 1):
                self._add(Incoming(self.keys.direct_secret(number), "direct", number=number))
            self.direct_highest = incoming.number
        return record

    def unspent(self):
        return [n for n in self.notes.values() if not n["spent"]]

    def to_json(self):
        return {"version": STATE_VERSION, "chain_id": self.chain_id, "pool": f"0x{self.pool:040x}",
                "account": self.keys.account, "owner_pk": hex32(self.keys.owner_pk),
                "scanned_block": self.scanned_block, "direct_highest": self.direct_highest,
                "tree": {str(e): n for e, n in sorted(self.tree.items())},
                "incoming": [{"secret": "0x" + i.secret.hex(), "kind": i.kind, "next_index": i.next_index,
                              "number": i.number} for i in self.incoming],
                "notes": sorted(self.notes.values(), key=lambda n: (n["epoch"], n["index"]))}

    @classmethod
    def from_json(cls, keys, data, gap=GAP, lookahead=LOOKAHEAD):
        if data.get("version") != STATE_VERSION or data.get("account") != keys.account or \
                int(data.get("owner_pk", "0x0"), 16) != keys.owner_pk:
            raise NotesError("the state file belongs to another wallet, account or format")
        scanner = cls.__new__(cls)
        scanner.keys, scanner.chain_id, scanner.pool = keys, int(data["chain_id"]), int(data["pool"], 16)
        scanner.gap, scanner.lookahead = gap, lookahead
        scanner.incoming, scanner.tags = [], {}
        for i in data["incoming"]:
            scanner._add(Incoming(bytes.fromhex(i["secret"][2:]), i["kind"], int(i["next_index"]),
                                  int(i["number"])))
        scanner.direct_highest = int(data["direct_highest"])
        scanner.tree = {int(e): int(n) for e, n in data["tree"].items()}
        scanner.notes = {(n["epoch"], n["index"]): n for n in data["notes"]}
        scanner.nullifiers = {int(n["nullifier"], 16): (n["epoch"], n["index"]) for n in data["notes"]}
        scanner.scanned_block = int(data["scanned_block"])
        return scanner


# ---- chain ----

LEAF_APPENDED = "0x" + w.keccak(b"LeafAppended(bytes32,uint64,uint32,bytes32)").hex()
NOTE_SPENT = "0x" + w.keccak(b"NoteSpent(bytes32)").hex()
NOTES = "0x" + w.keccak(b"Notes(bytes)").hex()


def decode_notes_data(data):
    """The bytes of a Notes(bytes) log's ABI-encoded data."""
    raw = bytes.fromhex(data.removeprefix("0x"))
    if len(raw) < 64 or int.from_bytes(raw[:32], "big") != 32:
        raise NotesError("malformed Notes log")
    length = int.from_bytes(raw[32:64], "big")
    if length not in SPEND_NOTES_BYTES + SHIELD_NOTE_BYTES or len(raw) < 64 + length:
        raise NotesError("malformed Notes log")
    return raw[64:64 + length]


def events_from_logs(logs):
    """Group the pool's logs into one Event per transaction, in chain order."""
    by_tx = {}
    for log in sorted(logs, key=lambda l: (int(l["blockNumber"], 16), int(l["transactionIndex"], 16),
                                           int(l["logIndex"], 16))):
        key = (int(log["blockNumber"], 16), int(log["transactionIndex"], 16))
        event = by_tx.setdefault(key, Event(key[0], b"", []))
        topic = log["topics"][0]
        if topic == LEAF_APPENDED:
            event.leaves.append((int(log["topics"][1], 16), int(log["topics"][2], 16),
                                 int(log["data"][2:66], 16)))
        elif topic == NOTE_SPENT:
            event.spent.append(int(log["topics"][1], 16))
        elif topic == NOTES:
            if event.notes:
                raise NotesError("a transaction published notes twice")
            event.notes = decode_notes_data(log["data"])
    return [by_tx[k] for k in sorted(by_tx)]


def fetch_logs(chain, pool, from_block, to_block, chunk=2_000):
    """The pool's LeafAppended, NoteSpent and Notes logs in [from_block, to_block]."""
    logs = []
    start = from_block
    while start <= to_block:
        end = min(start + chunk - 1, to_block)
        logs += chain.call("eth_getLogs", [{"address": f"0x{pool:040x}",
                                            "topics": [[LEAF_APPENDED, NOTE_SPENT, NOTES]],
                                            "fromBlock": hex(start), "toBlock": hex(end)}])
        start = end + 1
    return logs


# ---- files ----

def write_private(path, text):
    """Replace path with text in a new owner-only file, so no reader sees a partial
    state and an earlier world-readable copy is never reused."""
    path = Path(path)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
    try:
        with os.fdopen(fd, "w") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def read_private(path):
    """A file that holds secrets, refused if others may read it."""
    path = Path(path)
    if stat.S_IMODE(path.stat().st_mode) & 0o077:
        raise NotesError(f"{path} is readable by other users; chmod 600 it first")
    return path.read_text()


def parse_seed(text):
    try:
        seed = bytes.fromhex(text.strip().removeprefix("0x"))
    except ValueError:
        raise NotesError("a seed is hex") from None
    if len(seed) < MIN_SEED_BYTES:
        raise NotesError(f"a seed has at least {MIN_SEED_BYTES} bytes")
    return seed


def read_seed(seed_file):
    if seed_file:
        return parse_seed(read_private(seed_file))
    text = getpass.getpass("wallet seed (hex): ") if sys.stdin.isatty() else sys.stdin.readline()
    return parse_seed(text)


# ---- command line ----

def scan_command(args, keys):
    from disclosure import RpcChain, ReceiptError
    config = json.loads(Path(args.config).read_text())
    chain_id, pool = int(config["chainId"]), int(config["pool"], 16)
    chain = RpcChain(args.rpc or config["rpc"])
    try:
        if chain.chain_id() != chain_id:
            raise NotesError(f"the RPC is not on chain {chain_id}")
        state_path = Path(args.state)
        if state_path.exists():
            scanner = Scanner.from_json(keys, json.loads(read_private(state_path)))
            if (scanner.chain_id, scanner.pool) != (chain_id, pool):
                raise NotesError("the state file is for another chain or pool")
        else:
            scanner = Scanner(keys, chain_id, pool)
        start = max(scanner.scanned_block + 1, int(config.get("deploymentBlock", 0)))
        finalized = chain.finalized_block()
        for event in events_from_logs(fetch_logs(chain, pool, start, finalized, args.chunk)):
            scanner.scan(event)
        scanner.scanned_block = max(scanner.scanned_block, finalized)
    except ReceiptError as error:
        raise NotesError(str(error)) from None
    write_private(state_path, json.dumps(scanner.to_json(), indent=1))
    unspent = scanner.unspent()
    return {"scanned_block": scanner.scanned_block, "unspent": len(unspent),
            "balance": str(sum(n["value"] for n in unspent)),
            "notes": [{k: str(n[k]) if k == "value" else n[k] for k in ("cm", "epoch", "index", "value")}
                      for n in unspent]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["address", "direct-secret", "scan"])
    parser.add_argument("--seed-file", help="owner-only file holding the wallet seed in hex")
    parser.add_argument("--account", type=int, default=0, help="address number derived from the seed")
    parser.add_argument("--number", type=int, help="direct-secret: which secret to hand out")
    parser.add_argument("--config", help="scan: deployment config naming the chain and pool")
    parser.add_argument("--state", help="scan: wallet state file, created owner-only")
    parser.add_argument("--rpc", help="scan: RPC URL (default: the config's)")
    parser.add_argument("--chunk", type=int, default=2_000, help="scan: blocks per eth_getLogs call")
    args = parser.parse_args(argv)
    try:
        keys = WalletKeys(read_seed(args.seed_file), args.account)
        if args.command == "address":
            print(keys.address().hex())
        elif args.command == "direct-secret":
            if args.number is None:
                raise NotesError("direct-secret needs --number")
            print(json.dumps({"owner_pk": hex32(keys.owner_pk),
                              "secret": "0x" + keys.direct_secret(args.number).hex(),
                              "note": "send over a post-quantum channel; never publish it"}))
        else:
            if not args.config or not args.state:
                raise NotesError("scan needs --config and --state")
            print(json.dumps(scan_command(args, keys), indent=1))
    except (NotesError, OSError, KeyError, ValueError) as error:
        raise SystemExit(f"notes: {error}") from None


if __name__ == "__main__":
    main()
