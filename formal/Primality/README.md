# BN254 primality certificate

`PrattCertificate.lean` and `BN254.lean` are copied from
[Verified-zkEVM/CompPoly at 631e72b01d94d00d6096bed717d721774c5645d7](https://github.com/Verified-zkEVM/CompPoly/tree/631e72b01d94d00d6096bed717d721774c5645d7/CompPoly/Fields).
The original paths are `PrattCertificate.lean` and `BN254/Basic.lean`.
Copyright notices and the Apache 2.0 license are retained. The BN254 module's
import path is changed to this local `Primality` library.

The certificate proves primality through Mathlib's Lucas theorem. The search
tactic generates proof terms; its factoring or primality heuristics are not
trusted oracles. The Lean kernel checks the resulting certificate. This
provides the field property needed by the circuit gadget proofs (C1, C1c),
independently of the still-open bytecode bindings.


`BN254Base.lean` adds an explicit Pratt certificate for the distinct BN254
base modulus `q`. It uses the same checked Lucas machinery, with the large
factor chain written out to avoid repeated factoring. This supplies the Fq
field for `Groth16/Group.lean`; it proves no curve cardinality or subgroup fact.
