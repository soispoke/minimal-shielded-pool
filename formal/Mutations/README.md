# Circuit mutation certificates

All four circuit mutations required by SPEC.md §6 now have complete Lean
counterexamples. Each assignment satisfies every constraint of the compiled
mutant, while its exact canonical projections violate the named relation clause.

| Namespace under `MSP.Mutations` | Constraints | Relation failure |
|---|---:|---|
| `Membership` | 14,800 | R3: nonzero input with an invalid membership root |
| `Range` | 14,674 | R5: first input value equals 2^128 |
| `Duplicate` | 14,803 | R8: both nullifiers are equal |
| `Sink` | 14,796 | R7: zero output with a noncanonical inner commitment |

Each `Counterexample.lean` proves `counterexample`, an actual satisfying
assignment whose projections violate canonical `R`, and `c1_fails`, the failure
of C1 with that mutant system. `Soundness.original_c1_iff` checks that this
parameterized claim specializes exactly to the original C1. The axiom audit
pins each existential counterexample directly to the canonical relation and
projections and accepts only Lean's standard logical axioms.

`Check.lean` proves Boolean-checker reflection into the same constraint and
system semantics as the original circuit. A balanced witness table and blocks
of 512 constraints keep kernel evaluation bounded. Every block is certified
with ordinary `decide`; there is no native-evaluation axiom or admitted equation.

From `formal/`:

```sh
lake build Mutations Proofs.AxiomAudit
for case in membership range duplicate sink; do
  python3 tools/mutation_certificates.py --case "$case"
done
python3 -m unittest discover -s tools -p test_mutation_certificates.py
```

The exporter checks the full archived R1CS and WTNS hashes, exact source
mutation, independent JS constraint digest, and all 109 reused signal wire
positions. Add `--write` to regenerate each table and all constraint blocks.
The frozen artifacts and original compiler/witness runs are in
`../evidence/2026-09-27-0350/circuit-mutations/`.

The binary/source binding remains external to Lean. For only the four pinned
R1CS hashes, the exporter normalizes the known section-count header defect
from five to three in memory, then runs the unchanged strict parser. It also
compares every constraint with the independent archived decoder. No archived
artifact or canonical circuit is changed. The kernel proves the exported
systems' properties; it does not verify Circom or parse the R1CS binary.

The other model and chain mutation gates in SPEC.md remain open. These four
certificates do not discharge W2, chain execution or deployed-verifier binding.
