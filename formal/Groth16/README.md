# Pinned Groth16 key and proof encoding

`KeyData.lean` contains the exact verification key from the pinned JSON. Its
kernel certificate checks coordinate bounds, non-infinity and the curve
equations for alpha, all four IC points, beta, gamma and delta. The generator
first checks the complete SHA-256 pins and compares the JSON and Solidity
constants with the zkey's decoded points. It does not establish setup consistency.

`Encoding.lean` defines strict decoding of exactly 256 bytes into eight big-endian
words using `Spec.Basic.wordAt`. It rejects coordinates at least `q` and infinity
encodings, and proves that each G2 coordinate is read imaginary part first.
The decoder does not perform curve, subgroup or pairing verification.

`Curve.lean` defines modular coordinate arithmetic with `i² = -1`. The G2 check
is `(y²-x³)*(9+i)=3`. A kernel-checked inverse of `9+i` proves this is equivalent
to the ordinary twist equation. No field or curve-group laws are assumed.

From `formal/`:

```sh
lake build Groth16
python3 tools/groth16_key.py
python3 -m unittest discover -s tools -p test_groth16_key.py
```

To regenerate the exact key file, add `--write` to the generator command.
No ceremony is rerun and no proving artifact is changed.

`Primality/BN254Base.lean` proves the exact base modulus prime using an explicit
Pratt certificate. `Group.lean` supplies the actual Fq field and Mathlib's
proved nonsingular Weierstrass group for `y²=x³+3`, with canonical coordinate
round trips and the conventional base point `(1,2)`. It checks the discriminant
is nonzero; it does not assert the group's order.

Remaining mathematical bindings are the quadratic field and twist group,
prime-order subgroup membership and group order, and the pairing relation. `Spec.Circuit.Groth16Accepts` remains opaque. Its faithful definition
must combine these obligations with the strict encoding and the equation
`e(-A,B)·e(alpha,beta)·e(IC0+β·IC1+γ·IC2+α·IC3,gamma)·e(C,delta)=1`.
The three public scalars are ordered `(β,γ,α)`.

EIP-197 specifies the pairing check using discrete logarithms in its concrete
cyclic groups. A declarative version can follow that definition without a
Miller-loop implementation, but the group and subgroup bridges must still be
proved. See [EIP-197](https://eips.ethereum.org/EIPS/eip-197) and
[EIP-196](https://eips.ethereum.org/EIPS/eip-196).

The original powers-of-tau file is absent. This blocks the activation gate's
optional full snarkjs setup check, not this verification-key binding. The
canonical spec explicitly retains setup consistency and ceremony honesty as
P9 and P3 premises. Existing A/B metadata and key-coordinate comparisons do not
derive C/IC/L setup consistency, and neither these certificates nor a successful
full transcript check would establish ceremony honesty.
