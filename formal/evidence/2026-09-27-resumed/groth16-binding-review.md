# Concrete Groth16 binding review

Scope: `Groth16/TwistCardinality.lean`, `Groth16/Verifier.lean`,
`Spec/Circuit.lean` and `Proofs/Groth16Binding.lean`, against Claude's reviewed
round-37 C9 statement. This is a focused coordinator review, not an independent
reviewer or a proof of deployed execution.

The [normative EIP-197 definition](https://eips.ethereum.org/EIPS/eip-197#specification)
uses the sum of products of logarithms in the two specified generators.
Both generators' exact coordinates match the definitions here. Their scalar
isomorphisms now have checked inverses, so the logarithms reconstruct every
point with a representative below `p`. G1 is the entire base-field curve;
G2 is exactly the twist subgroup killed by `p`. Its cardinality is proved,
not assumed or inferred from only the key's point orders.

The decoder requires exactly 256 bytes, reads G2 imaginary coordinates first,
rejects coordinates at least `q`, and rejects all three infinity encodings.
`Accepts` also requires every curve equation and G2 membership. Checked G1
cardinality supplies A/C membership. `groth16_accepts_point_orders` proves
all accepted finite points have exact order `p`.

The pinned Solidity source's `checkPairing` at lines 103–159 forms
`IC0 + beta*IC1 + gamma*IC2 + alpha*IC3` and pairs `(-A,B)`,
`(keyAlpha,keyBeta)`, `(publicPoint,keyGamma)` and `(C,keyDelta)`.
`VerificationEquation` uses precisely those terms; its algebraic rearrangement
is proved. The existing key generator binds every used key coordinate to the
pinned JSON, zkey and Solidity constants. The predicate makes no assumption
about which public inputs have witnesses, and does not assert extraction or
prover completeness. P3/P3c/P9 remain explicit canonical premises.

The definition closure is statement-locked and all principal statements are
standard-axiom audited. No executable verifier, bytecode behavior, resource
bound or C9 proof is inferred from this transcription review. The pending
`verifierOf` binding must execute the linked artifact; substituting this
predicate there would make the required equivalence circular.
