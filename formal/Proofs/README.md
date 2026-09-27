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
| `Model.lean` | `C1 → C5g P`, `C1 → C5h P`, `C1 → Spendable P`, and `model_theorem_of` |
| `Effects.lean` | `C5k P`, `C1 → C5j P`, `C1 → C5l P`, `C5m P`, `C5n P`, `StepFunctional P`, and `model_theorem : ModelTheorem` |
| `Composes.lean` | `MSP.composes : Composes`, connecting the expanded `MainTheorem` to `ChainCorollary` |
| `Composition.lean` | compatibility module for the earlier composition imports |
| `CircuitArithmetic.lean` | field equality implies integer conservation under the six specified value bounds |
| `CircuitGadgets.lean` | BN254 scalar primality, Boolean and IsZero gadget lemmas, and Num2Bits range soundness |
| `PoseidonConstants.lean` | kernel-checked equality of all 21 zero-tree constants with concrete Poseidon |
| `C6.lean` | `MSP.c6 : C6`, for the specified incremental-tree algorithm and concrete Poseidon |
| `../Artifacts/CircuitSoundness.lean` | `MSP.c1 : C1`, for the complete pinned R1CS and concrete projections |
| `CircuitCompleteness.lean` | canonical Boolean witness construction |
| `../Artifacts/CircuitCompleteness.lean` | `MSP.c1c : C1c`, complete pinned-R1CS assignment construction with exact projections |
| `CircuitModel.lean` | discharged circuit/model conjunction; the main theorem and chain corollary from the remaining chain obligations |
| `AxiomAudit.lean` | build-time admission checks for the principal proofs, including full-R1CS compression |

`ModelTheorem` is proven: every model claim holds for every pool from C1.
C1 and C1c are now discharged for the pinned circuit. `Composes` and C6 are also proven. C6 establishes the Lean tree algorithm;
refinement of the actual bytecode to that algorithm remains open.

[The artifact proofs](../Artifacts/README.md) derive the entire canonical
relation and both compression outputs from the complete pinned R1CS.
`Spec.Circuit`'s six circuit declarations are now concrete definitions;
`CircuitSoundness` proves the unchanged C1 statement. All 54 small-hash
instances, the beta gadget, all range/control/path gates and the private
projection are connected. Universal optimized/reference Poseidon equivalence
is proved for all three widths. Keccak and Groth16 verification remain opaque.

`CircuitCompleteness` assembles actual complete hash, range, path, control and
compression witnesses using checked wire ownership and shared-value agreement.
Its exact ordered coverage accounts for every pinned constraint. The result
preserves all private witness fields and works for every alpha.

Remaining completion gates include C2/C2c/C8/C9/C10 and refinement,
the required concrete key/verifier/library/bytecode bindings, W1/W2, and the
semantic mutation failures in `SPEC.md`. The decoder's negative tests do not
discharge those mutation gates. End-to-end formal verification is incomplete.


`NonVacuityBytes` proves the concrete big-endian word round trips.
`NonVacuityEncoding` constructs the actual three-frame calldata and proves
all A1–A7 checks from explicit field bounds, proof checks and verifier acceptance.
These reusable encoding lemmas support W1; they do not themselves prove an
accepted run, no bad event or any chain-level non-vacuity claim.

The specification's `K` is now the concrete Ethereum Keccak definition in
`Keccak/`. Its fixed source/domain digests have kernel certificates.
The key and strict proof-decoding layer in `Groth16/` is also checked; pairing,
subgroup and deployed-bytecode binding remain separate obligations.


`NonVacuityFixtureVerified.lean` proves `MSP.w1 : W1` with no hypotheses.
The witness shields two units, publishes epoch zero's root, advances one slot,
and spends: one unit pays gas and one becomes withdrawal credit, with both
outputs equal to their designated sinks. C1c supplies the actual pinned-R1CS
assignment. The ideal verifier accepts exactly satisfying public triples and
its extractor is correct for all accepted proofs, as W1 requires.

The complete bad-event predicate is checked. Symbolic membership equivalence
compresses empty subtrees without discarding any distinct query. The table
contains 74 Poseidon entries and six Keccak/domain entries, including repeated
queries, with kernel-checked values, all cross-table collisions and all
nondegeneracy checks. It covers both input paths, including the dummy path,
all historical tree prefixes and every storage/nonce/source query in the run.
Exact assignment projections discharge compression and extraction failures.
This is model non-vacuity; no claim/payout or chain-level W2 is inferred.
