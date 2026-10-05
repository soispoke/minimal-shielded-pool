"""BabyJubjub and circomlib's EdDSA-Poseidon in plain Python.

The curve is circomlib's babyjub.circom over the BN254 scalar field,
a*x^2 + y^2 = 1 + d*x^2*y^2 with a = 168700 and d = 168696. Its prime-order
subgroup has order L and generator B8, eight times circomlib's generator.

`verify` checks what the spend circuit checks: both points on the curve (its
BabyCheck components) and circomlib's EdDSAPoseidonVerifier, which requires
S < L, 8*A not the identity, and S*B8 == R8 + h*(8*A) for the challenge
h = Poseidon(R8x, R8y, Ax, Ay, M) taken as a whole field element.

`sign` makes such a signature with a secret scalar a, where A = a*B8:
S = r + 8*h*a mod L. Its nonce r is BLAKE2b of the secret and the message, so
signing needs no randomness and one key never reuses a nonce across messages.
circomlibjs, and the Ledger apps that reproduce it, derive keys and nonces
from a 32-byte seed with BLAKE-512 instead. Verification depends only on the
equation, so their signatures verify here and these verify there.

`python3 babyjubjub.py` checks the circomlibjs signatures and the pool chain's
spend authorization in ../vectors/poseidon_bn254_vectors.json.
"""
import hashlib
import json
from pathlib import Path

from poseidon_bn254 import P, TAG_AUTH, p2, poseidon

A_COEFF, D_COEFF = 168700, 168696
L = 2736030358979909402780800718157159386076813972158567259200215660948447373041
B8 = (5299619240641551281634865583518297030282874472190772894086521144482721001553,
      16950150798460657717958625567821834550301663161624707787222815936182638968203)
IDENTITY = (0, 1)


def on_curve(point):
    x, y = point
    if not (0 <= x < P and 0 <= y < P):
        return False
    xx, yy = x * x % P, y * y % P
    return (A_COEFF * xx + yy) % P == (1 + D_COEFF * xx * yy) % P


def add(p1, p2):
    """Twisted Edwards addition, complete on the curve (circomlib's BabyAdd)."""
    (x1, y1), (x2, y2) = p1, p2
    t = D_COEFF * x1 * x2 * y1 * y2 % P
    x3 = (x1 * y2 + y1 * x2) * pow(1 + t, -1, P) % P
    y3 = (y1 * y2 - A_COEFF * x1 * x2) * pow(1 - t, -1, P) % P
    return x3, y3


def mul(point, k):
    """k * point by double-and-add; k may be any non-negative integer."""
    result = IDENTITY
    while k:
        if k & 1:
            result = add(result, point)
        point = add(point, point)
        k >>= 1
    return result


def public_key(secret):
    """A = a*B8 for a secret scalar 0 < a < L."""
    if not 0 < secret < L:
        raise ValueError("spending key must be a scalar in [1, L)")
    return mul(B8, secret)


def challenge(r8, pub, message):
    return poseidon([r8[0], r8[1], pub[0], pub[1], message])


def sign(secret, message):
    """EdDSA-Poseidon signature (R8x, R8y, S) on a field element."""
    if not 0 <= message < P:
        raise ValueError("message must be a field element")
    pub = public_key(secret)
    seed = hashlib.blake2b(secret.to_bytes(32, "big") + message.to_bytes(32, "big"),
                           digest_size=64, person=b"msp-eddsa-nonce").digest()
    r = int.from_bytes(seed, "big") % L or 1
    r8 = mul(B8, r)
    s = (r + 8 * challenge(r8, pub, message) * secret) % L
    return r8[0], r8[1], s


def verify(pub, message, signature):
    """Whether the spend circuit accepts this signature by pub on message."""
    r8x, r8y, s = signature
    r8 = (r8x, r8y)
    if not (on_curve(pub) and on_curve(r8) and 0 <= s < L and 0 <= message < P):
        return False
    pub8 = mul(pub, 8)
    if pub8[0] == 0:  # 8*A is the identity: any R8 = S*B8 would verify
        return False
    return mul(B8, s) == add(r8, mul(pub8, challenge(r8, pub, message)))


def _check():
    vecs = json.loads((Path(__file__).parent.parent / "vectors" /
                       "poseidon_bn254_vectors.json").read_text())
    for v in vecs["eddsa_poseidon"]:
        v = {k: int(x) for k, x in v.items()}
        pub, sig = (v["Ax"], v["Ay"]), (v["R8x"], v["R8y"], v["S"])
        assert verify(pub, v["M"], sig), "circomlibjs signature rejected"
        assert not verify(pub, (v["M"] + 1) % P, sig), "signature accepted for another message"
        assert not verify(pub, v["M"], (sig[0], sig[1], sig[2] + L)), "unreduced S accepted"
    c = {k: int(x) for k, x in vecs["pool_chain"].items()}
    assert c["auth_message"] == p2(TAG_AUTH, c["beta"]), "auth message mismatch"
    assert verify((c["spend_Ax"], c["spend_Ay"]), c["auth_message"],
                  (c["auth_R8x"], c["auth_R8y"], c["auth_S"])), "pool chain authorization rejected"
    secret = 0x1234567890abcdef % L
    message = c["auth_message"]
    sig = sign(secret, message)
    assert verify(public_key(secret), message, sig) and sign(secret, message) == sig
    assert not verify(public_key(secret + 1), message, sig), "signature accepted under another key"
    # Small-order keys: 8*A is the identity, so S*B8 == R8 forges for anyone.
    forged = mul(B8, 5)
    for weak in (IDENTITY, (0, P - 1)):
        assert on_curve(weak) and not verify(weak, message, (forged[0], forged[1], 5))
    print(f"babyjubjub.py matches circomlibjs: {len(vecs['eddsa_poseidon'])} signatures + "
          "pool chain authorization + local signing")


if __name__ == "__main__":
    _check()
