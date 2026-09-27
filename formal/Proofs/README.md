# Proof status

The model proofs were developed with abstract hashes and now build against
the concrete reference Poseidon definitions in `Spec/Hash.lean`. Keccak remains
opaque. The claims retain their bad-event alternatives and C1 hypotheses.
`lake build` checks the proofs; `AxiomAudit.lean` rejects dependencies outside
Lean's standard logical axioms for the principal results listed below.

| File | Proves |
|---|---|
| `C5d.lean` | `C5d P` for every pool |
| `C3.lean` | `C5e P` for every pool, and `C1 → C3 P` |
| `C5a.lean` | `C1 → C5a P` |
| `C5cC4.lean` | `C1 → C5b P → C5c P`, and `C1 → C5b P → C5c P → C4 P` |
| `Path.lean` | the path walk: a Merkle path whose root is `TR L`, without a collision against `L`'s tree queries, starts at `L`'s leaf |
| `C5i.lean` | `C5b P → C5i P` |
| `C5b.lean` | `C1 → C5b P` |
| `Model.lean` | `C1 → C5g P`, `C1 → C5h P`, `C1 → Spendable P`, and `model_theorem : ModelTheorem` |
| `Composition.lean` | `MSP.composes : Composes`, connecting `MainTheorem` to `ChainCorollary` |
| `CircuitArithmetic.lean` | field equality implies integer conservation under the six specified value bounds |
| `CircuitGadgets.lean` | BN254 scalar primality, Boolean and IsZero gadget lemmas, and Num2Bits range soundness |
| `PoseidonConstants.lean` | kernel-checked equality of all 21 zero-tree constants with concrete Poseidon |
| `C6.lean` | `MSP.c6 : C6`, for the specified incremental-tree algorithm and concrete Poseidon |
| `AxiomAudit.lean` | build-time admission checks for the principal proofs, including full-R1CS compression |

`ModelTheorem` is proven: every model claim holds for every pool from C1.
`Composes` and C6 are also proven. C6 establishes the Lean tree algorithm;
refinement of the actual bytecode to that algorithm remains open.

[The artifact proofs](../Artifacts/README.md) establish the compression
polynomial and the first input's 128-bit bound from the complete pinned R1CS.
They do not yet establish its beta
digest, the complete spend relation, or C1/C1c. The arithmetic and gadget
lemmas above are reusable proof components, not a substitute for that binding.
[The concrete Poseidon definitions](../Poseidon/README.md) still require a
proof of equivalence with the optimized circuit and deployed libraries.

Remaining completion gates include C1/C1c, C2/C2c/C8/C9/C10 and refinement,
the required concrete key/verifier/library/bytecode bindings, W1/W2, and the
semantic mutation failures in `SPEC.md`. The decoder's negative tests do not
discharge those mutation gates. End-to-end formal verification is incomplete.
