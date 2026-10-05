"""Wallet and indexer for the BN254 join-split shielded pool.

Value-carrying notes: cm = Poseidon(TAG_LEAF, inner, value) with
inner = Poseidon2(owner_pk, rho) and owner_pk = Poseidon(TAG_PK, Ax, Ay, nk).
A = (Ax, Ay) is a BabyJubjub spending key whose private half only a signer
holds, such as a hardware wallet; nk, the note's nullifying key, and rho stay
with the wallet and cannot spend. A recipient reveals only `inner` (never the
secrets); the payer chooses the value, and `shield` hashes msg.value into the
commitment on-chain, so a deposit's value is what was actually deposited.

A spend consumes two inputs owned by one spending key (a zero-value dummy
stands in when only one real note is spent) and creates two outputs.
`build_witness` asks the signer to sign the statement, checks the signature,
and returns the circom input map that ../tooling proves with snarkjs against
build/spend_final.zkey. The prover never sees the spending key.
"""
import random
import secrets
import sys
from pathlib import Path

from eth_hash.auto import keccak

sys.path.insert(0, str(Path(__file__).parent.parent / "reference"))
import babyjubjub as bjj  # noqa: E402
from poseidon_bn254 import P, TAG_AUTH, p2, poseidon, tagged, TAG_PK, TAG_LEAF  # noqa: E402

DEPTH = 20
MAX_VALUE = 1 << 128
# keccak256(b"minimal-shielded-pool:occurrence-domain:v1"). Fresh deployment only.
DOMAIN_TAG = bytes.fromhex("a9d03fa1cd97bcf3294dc8e3bb024f555393c98967b356967fa502abab366ed3")
TAG_OCCURRENCE_NULL = 4
SINK_INNERS = (1, 2)
SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

_RNG = None  # None = cryptographic secrets; set_seed makes note generation reproducible


def set_seed(seed):
    """Make note generation deterministic (for reproducible fixtures/tests)."""
    global _RNG
    _RNG = random.Random(seed)


def rand_fe():
    """A uniformly random field element."""
    if _RNG is None:
        return secrets.randbelow(P)
    return _RNG.randrange(P)


# ---- note cryptography (mirrors ../circuits/spend.circom) ----

def owner_pk(pub, nk):
    """The note owner: the spending key's public half and the note's nullifying key."""
    return poseidon([TAG_PK, pub[0], pub[1], nk])


def inner(pub, nk, rho):
    """What a recipient reveals to be paid: hides owner_pk and rho."""
    return p2(owner_pk(pub, nk), rho)


def commitment(pub, nk, rho, value):
    return tagged(TAG_LEAF, inner(pub, nk, rho), value)


def domain_scalar(chain_id, pool_address, epoch=0):
    """Domain for an authenticated input epoch, not the current output epoch."""
    if isinstance(pool_address, str):
        pool_address = bytes.fromhex(pool_address.removeprefix("0x"))
    elif isinstance(pool_address, int):
        pool_address = pool_address.to_bytes(20, "big")
    if len(pool_address) != 20 or not 0 <= chain_id < 1 << 256 or not 0 <= epoch < 1 << 64:
        raise ValueError("domain inputs must be uint256 chain_id, address20 pool and uint64 epoch")
    padded_pool = bytes(12) + pool_address
    return int.from_bytes(keccak(DOMAIN_TAG + chain_id.to_bytes(32, "big") + padded_pool
                                 + epoch.to_bytes(32, "big")), "big") % P


def nullifier(domain, nk, cm, index):
    if not 0 <= index < 1 << DEPTH:
        raise ValueError("note index outside the depth-20 tree")
    return tagged(TAG_OCCURRENCE_NULL, p2(domain, nk), p2(cm, index))


def new_note():
    """Fresh (nk, rho); the wallet keeps both secret. A fresh nk per note keeps
    one disclosed nullifier key from revealing the owner's other spends."""
    return rand_fe(), rand_fe()


class SoftwareSigner:
    """A spending key held in this process: the stand-in for a hardware wallet
    in fixtures and tests. A hardware signer offers the same two members, the
    public key and a signature over one field element."""

    def __init__(self, secret):
        self.secret = secret
        self.public_key = bjj.public_key(secret)

    def sign(self, message):
        return bjj.sign(self.secret, message)


def new_signer():
    """A fresh software spending key."""
    if _RNG is None:
        return SoftwareSigner(secrets.randbelow(bjj.L - 1) + 1)
    return SoftwareSigner(_RNG.randrange(1, bjj.L))


def new_authorizer():
    """Fresh one-time secp256k1 key and its Ethereum address as an integer."""
    from eth_keys import keys
    if _RNG is None:
        secret = secrets.randbelow(SECP256K1_N - 1) + 1
    else:
        secret = _RNG.randrange(1, SECP256K1_N)
    raw = secret.to_bytes(32, "big")
    key = keys.PrivateKey(raw)
    return "0x" + raw.hex(), int.from_bytes(key.public_key.to_canonical_address(), "big")


def dummy_input():
    """A zero-value dummy input: fabricated secrets, never in the tree. Its
    nullifier derives from its own fabricated cm, so it cannot collide with a
    real note's, and it contributes zero to conservation. It is owned by the
    spend's key like the real input, since one signature covers both."""
    nk, rho = new_note()
    return {"nk": nk, "rho": rho, "value": 0, "idx": None}


# ---- the tree / indexer ----

class Tree:
    """Full zero-padded Merkle tree of note commitments, matching the pool."""

    def __init__(self, depth=DEPTH):
        self.depth = depth
        self.leaves = []
        self.zeros = [0]
        for _ in range(depth):
            self.zeros.append(p2(self.zeros[-1], self.zeros[-1]))

    def append(self, cm):
        idx = len(self.leaves)
        assert idx < (1 << self.depth), "tree full"
        self.leaves.append(cm)
        return idx

    def _levels(self):
        level = list(self.leaves) if self.leaves else [self.zeros[0]]
        levels = [level]
        for d in range(self.depth):
            nxt = []
            for i in range(0, len(level), 2):
                left = level[i]
                right = level[i + 1] if i + 1 < len(level) else self.zeros[d]
                nxt.append(p2(left, right))
            level = nxt
            levels.append(level)
        return levels

    def root(self):
        return self._levels()[self.depth][0]

    def auth_path(self, idx):
        levels = self._levels()
        siblings, bits = [], []
        for d in range(self.depth):
            level = levels[d]
            sib_idx = idx ^ 1
            sib = level[sib_idx] if sib_idx < len(level) else self.zeros[d]
            siblings.append(sib)
            bits.append(idx & 1)
            idx >>= 1
        return siblings, bits


# ---- witness building ----

def address_scalar(addr_hex):
    """An Ethereum address represented as its canonical field element."""
    h = addr_hex[2:] if addr_hex.startswith("0x") else addr_hex
    return int(h, 16)


def sink_outputs():
    """The two position-specific canonical zero outputs."""
    return [(SINK_INNERS[0], 0), (SINK_INNERS[1], 0)]


def sink_commitments():
    return [tagged(TAG_LEAF, SINK_INNERS[i], 0) for i in range(2)]


def opens(tree, cm, idx):
    """Whether cm sits at leaf idx of the tree, by its authentication path."""
    siblings, bits = tree.auth_path(idx)
    node = cm
    for sibling, bit in zip(siblings, bits):
        node = p2(sibling, node) if bit else p2(node, sibling)
    return node == tree.root()


def build_witness(
    tree, inputs, outputs, domain, *, signer, authorizer, public_amount=0, fee=0,
    recipient=None,
):
    """A join-split witness against the current tree, as the circom input map.

    inputs: exactly two dicts {nk, rho, value, idx} owned by signer's key (idx
            None for a dummy, which must have value 0). Use dummy_input() to pad.
    outputs: exactly two (inner, value) pairs.
    signer: holds the spending key; signs the statement (see sign_witness).
    Values must conserve: sum(in) == sum(out) + public_amount + fee.
    """
    assert len(inputs) == 2 and len(outputs) == 2
    assert any(i["value"] > 0 for i in inputs), "at least one real input is required"
    assert all(i["idx"] is not None or i["value"] == 0 for i in inputs), \
        "a dummy input must have value 0"
    total_in = sum(i["value"] for i in inputs)
    total_out = sum(v for _, v in outputs) + public_amount + fee
    assert total_in == total_out, f"not conserved: {total_in} != {total_out}"
    assert all(0 <= v < MAX_VALUE for v in
               [public_amount, fee] + [i["value"] for i in inputs] + [v for _, v in outputs])
    assert 0 < authorizer < 1 << 160
    for k, (out_inner, value) in enumerate(outputs):
        if value == 0:
            assert out_inner == SINK_INNERS[k], "zero output must use its positional sink"
        else:
            assert out_inner not in SINK_INNERS, "positive output uses a reserved sink inner"
    assert output_commitments(outputs)[0] != output_commitments(outputs)[1], \
        "output commitments must be distinct"

    recipient_value = address_scalar(recipient) if recipient is not None else 0
    pub = signer.public_key
    for i in inputs:
        assert i["idx"] is None or opens(tree, commitment(pub, i["nk"], i["rho"], i["value"]), i["idx"]), \
            f"leaf {i['idx']} is not this opening under the signer's key"
    nf1, nf2 = input_nullifiers(domain, pub, inputs)
    out_cm1, out_cm2 = output_commitments(outputs)
    alpha = compression_alpha(statement(nf1, nf2, out_cm1, out_cm2, tree.root(), domain,
                                        public_amount, fee, recipient_value, authorizer))
    sibs, bits = [], []
    for i in inputs:
        if i["idx"] is None:
            sibs.append([0] * tree.depth)
            bits.append([0] * tree.depth)
        else:
            s, b = tree.auth_path(i["idx"])
            sibs.append(s)
            bits.append(b)
    return sign_witness({
        "alpha": str(alpha),
        "root": str(tree.root()),
        "domain": str(domain),
        "Ax": str(pub[0]),
        "Ay": str(pub[1]),
        "in_nk": [str(i["nk"]) for i in inputs],
        "in_rho": [str(i["rho"]) for i in inputs],
        "in_value": [str(i["value"]) for i in inputs],
        "in_siblings": [[str(x) for x in s] for s in sibs],
        "in_bits": [[str(x) for x in b] for b in bits],
        "out_inner": [str(inn) for inn, _ in outputs],
        "out_value": [str(v) for _, v in outputs],
        "public_amount": str(public_amount),
        "fee": str(fee),
        "recipient": str(recipient_value),
        "authorizer": str(authorizer),
    }, signer)


def witness_statement(witness):
    """The ten statement values the circuit computes from a witness map,
    whatever its path bits: what a signature over the witness must cover."""
    def field(key, k=None):
        return int(witness[key] if k is None else witness[key][k]) % P

    pub, domain = (field("Ax"), field("Ay")), field("domain")
    nfs = []
    for k in range(2):
        cm = commitment(pub, field("in_nk", k), field("in_rho", k), field("in_value", k))
        index = sum(int(b) << i for i, b in enumerate(witness["in_bits"][k])) % P
        nfs.append(tagged(TAG_OCCURRENCE_NULL, p2(domain, field("in_nk", k)), p2(cm, index)))
    outs = output_commitments([(field("out_inner", k), field("out_value", k)) for k in range(2)])
    return statement(*nfs, *outs, field("root"), domain, field("public_amount"), field("fee"),
                     field("recipient"), field("authorizer"))


def auth_message(stmt):
    """The field element the spending key signs: Poseidon2(TAG_AUTH, beta)."""
    return p2(TAG_AUTH, compression_beta(stmt))


def sign_witness(witness, signer):
    """The witness with the spending key's signature over its statement. The
    signature is checked here before proving: a signer, a hardware wallet
    included, is a source of input to validate, not an authority."""
    message = auth_message(witness_statement(witness))
    signature = signer.sign(message)
    pub = (int(witness["Ax"]), int(witness["Ay"]))
    if not bjj.verify(pub, message, signature):
        raise ValueError("the signer's signature does not verify for this spend's key and statement")
    r8x, r8y, s = signature
    return dict(witness, R8x=str(r8x), R8y=str(r8y), S=str(s))


def statement(nf1, nf2, out_cm1, out_cm2, root, domain, public_amount, fee,
              recipient, authorizer):
    """The ten statement values, in the order the circuit and the pool hash them."""
    return [nf1, nf2, out_cm1, out_cm2, root, domain, public_amount, fee,
            recipient, authorizer]


def compression_alpha(stmt):
    """Hybrid compression's contract-side hash: keccak256 of the ten values as
    32-byte words, reduced into the scalar field. The pool computes the same."""
    assert len(stmt) == 10 and all(0 <= x < P for x in stmt)
    return int.from_bytes(keccak(b"".join(x.to_bytes(32, "big") for x in stmt)), "big") % P


def compression_beta(stmt):
    """Hybrid compression's circuit-side hash: circomlib Poseidon of the ten values."""
    assert len(stmt) == 10
    return poseidon(stmt)


def fingerprint(sigma, stmt):
    """x[0] + x[1]*sigma + ... + x[9]*sigma^9 mod P, by Horner's rule."""
    acc = 0
    for x in reversed(stmt):
        acc = (acc * sigma + x) % P
    return acc


def input_nullifiers(domain, pub, inputs):
    """The two nullifiers a witness's inputs, owned by pub, expose, in order."""
    return [nullifier(domain, i["nk"], commitment(pub, i["nk"], i["rho"], i["value"]),
                      i["idx"] if i["idx"] is not None else 0) for i in inputs]


def output_commitments(outputs):
    return [tagged(TAG_LEAF, inn, v) for inn, v in outputs]


def _selfcheck():
    """The wallet tree must agree with the exported incremental-tree fixture,
    and a value note's auth path must reproduce the root."""
    import json
    fx = json.loads((Path(__file__).parent.parent / "vectors"
                     / "poseidon_bn254_vectors.json").read_text())["tree"]
    t = Tree()
    assert t.root() == int(fx["root_empty"]), "empty root mismatch"
    t.append(int(fx["cm0"]))
    assert t.root() == int(fx["root_after_cm0"]), "root after cm0 mismatch"
    t.append(int(fx["cm1"]))
    assert t.root() == int(fx["root_after_cm0_cm1"]), "root after cm0,cm1 mismatch"

    nk, rho = new_note()
    cm = commitment(new_signer().public_key, nk, rho, 10**18)
    t2 = Tree()
    i = t2.append(cm)
    sibs, bits = t2.auth_path(i)
    node = cm
    for b, s in zip(bits, sibs):
        node = p2(node, s) if b == 0 else p2(s, node)
    assert node == t2.root(), "auth path does not reproduce the root"
    print("wallet.py OK: tree matches the exported fixture; value-note paths verify")


if __name__ == "__main__":
    _selfcheck()
