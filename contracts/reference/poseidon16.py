"""Reference implementation of leanVM's Poseidon16 in plain Python.

This is the hash the spend circuit actually uses: classic Poseidon (not
Poseidon2) over KoalaBear (p = 2^31 - 2^24 + 1), width 16, x^3 S-box,
4 initial full rounds + 20 partial rounds + 4 terminal full rounds, circulant
MDS matrix M[i][j] = COL[(i - j) mod 16], and compression defined as
compress(x) = (permute(x) + x)[0:8]. Constants are transcribed from
leanVM commit 12e6151, crates/backend/koala-bear/src/poseidon1_koalabear_16.rs
(there named Poseidon1KoalaBear16; the optimized sparse partial rounds in that
file are an equivalent rewrite of the naive rounds implemented here).

`python3 poseidon16.py` checks every vector in ../vectors/poseidon16_vectors.json
(exported from leanVM itself, see ../vectors/README.md), including the pool's
tagged owner_pk / cm / nf / claim chain. This file is the wallet-side building
block and the source the Solidity library is checked against.
"""
import json
from pathlib import Path

P = 2**31 - 2**24 + 1                     # KoalaBear
COL = [1, 3, 13, 22, 67, 2, 15, 63, 101, 1, 2, 17, 11, 1, 51, 1]
HALF_FULL, PARTIAL = 4, 20
_RC_PATH = Path(__file__).parent / "round_constants.json"
RC = json.loads(_RC_PATH.read_text())     # 28 rounds x 16 constants
assert len(RC) == 28 and all(len(r) == 16 for r in RC)


def _mds(s):
    return [sum(COL[(i - j) % 16] * s[j] for j in range(16)) % P for i in range(16)]


def permute(state):
    """The Poseidon16 permutation on a list of 16 field elements."""
    s = [x % P for x in state]
    for r in range(28):
        s = [(x + c) % P for x, c in zip(s, RC[r])]
        if HALF_FULL <= r < HALF_FULL + PARTIAL:
            s[0] = pow(s[0], 3, P)        # partial round: S-box on lane 0 only
        else:
            s = [pow(x, 3, P) for x in s]  # full round: S-box on every lane
        s = _mds(s)
    return s


def compress(x16):
    """16 -> 8 compression: permute, feed the input forward, truncate."""
    y = permute(x16)
    return [(a + b) % P for a, b in zip(y[:8], x16[:8])]


def compress_pair(a8, b8):
    return compress(list(a8) + list(b8))


# ---- the pool's tagged-hash shapes (mirrors circuits/spend.py) ----
TAG_PK, TAG_LEAF, TAG_NULL, TAG_CLAIM = 1, 2, 3, 4
ZERO8 = [0] * 8


def tagged(tag, a8, b8):
    inner = compress_pair(a8, b8)
    return compress_pair([tag] + [0] * 7, inner)


def pack(d8):
    """Canonical digest encoding: 8 big-endian 32-bit words -> 32 bytes."""
    return b"".join(int(x).to_bytes(4, "big") for x in d8)


def unpack(b32):
    assert len(b32) == 32
    out = [int.from_bytes(b32[i:i + 4], "big") for i in range(0, 32, 4)]
    assert all(x < P for x in out), "not a canonical digest encoding"
    return out


def _check():
    vecs = json.loads((Path(__file__).parent.parent / "vectors" /
                       "poseidon16_vectors.json").read_text())
    for v in vecs["permute"]:
        assert permute(v["in"]) == v["out"], "permute vector mismatch"
    for v in vecs["compress"]:
        assert compress(v["in"]) == v["out"], "compress vector mismatch"
    c = vecs["pool_chain"]
    owner_pk = tagged(TAG_PK, c["spend_key"], ZERO8)
    assert owner_pk == c["owner_pk"], "owner_pk mismatch"
    cm = tagged(TAG_LEAF, owner_pk, c["rho"])
    assert cm == c["cm"], "cm mismatch"
    nf = tagged(TAG_NULL, c["spend_key"], cm)
    assert nf == c["nf"], "nf mismatch"
    claim = tagged(TAG_CLAIM, compress_pair(c["root"], nf),
                   compress_pair(c["out_cm"], c["ctx"]))
    assert claim == c["claim"], "claim mismatch"
    assert unpack(pack(claim)) == claim
    n = len(vecs["permute"]) + len(vecs["compress"])
    print(f"poseidon16.py matches leanVM: {n} vectors + pool chain (owner_pk, cm, nf, claim)")


if __name__ == "__main__":
    _check()
