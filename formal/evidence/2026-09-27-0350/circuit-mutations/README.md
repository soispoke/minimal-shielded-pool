# Circuit mutation counterexamples

All four circuit mutations required by `formal/SPEC.md` admit an invalid spend.
Each generated witness satisfies every constraint of its compiled mutant under
both `snarkjs.wtns.check` and independent Python modular evaluation. The pinned
original circuit's WASM witness generator rejects the same input at the expected
assertion. The unmodified baseline accepts its valid input and reproduces the
exact pinned R1CS and symbol hashes.

| Source change | Checked constraints | Only false relation clause | Original rejection |
| --- | ---: | --- | --- |
| None, valid baseline | 14,802 | None | Accepted |
| Remove value-gated membership | 14,800 | R3: positive input has the wrong root | `InputNote`, line 127 |
| Skip only `rc[0]` | 14,674 | R5: first input is `2^128` | `Num2Bits`, line 38 |
| Remove nullifier inequality | 14,803 | R8: identical input nullifiers | `Spend`, line 247 |
| Remove zero/positive sink rules | 14,796 | R7: zero output has inner `3` | `Spend`, line 197 |

The duplicate-nullifier mutant has one more constraint because compilation no
longer folds the `IsEqual` result to zero. These counts describe the actual
compiled systems, not an assumed count of deleted source assertions.

The baseline uses keys and randomness `[1, 2]`, input values `[2, 0]`, indices
zero, a valid first path with the depth-20 zero hashes, and an unconstrained
dummy path of zeros. Outputs are the two zero sinks; public amount, fee,
recipient, authorizer, and domain are `1`; alpha is `0`. Mutation inputs change
only what their counterexample needs. Membership uses root zero. The range
counterexample uses input `2^128`, output value `2^128 - 1` with inner `3`, and
public amount/recipient zero, retaining exact integer conservation. The duplicate
case spends the same value-1 note twice at the same index/path. The sink case
changes the first zero output's inner from `1` to `3`.

For every case, the checker reads the actual witness statement outputs and all
surviving source wires. It reconstructs the eliminated fee by the concrete
conservation projection. Independent reference Poseidon recomputes the note
commitments, paths, nullifiers, outputs, and compression. All nine canonical
relation clauses are evaluated on these values; `result.json` records each
boolean, the individual amount bounds, integer conservation, computed roots,
statement, and public signals.

## Reproduce

From the repository root, with Python 3.10 or later and the pinned local Node
dependencies:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/homebrew/bin/python3.13 formal/tools/circuit_mutations.py \
  --node-modules /Volumes/PrivateAI/WorkRepos/minimal-shielded-pool/tooling/node_modules \
  --evidence /private/tmp/msp-circuit-mutations-recheck
PYTHONDONTWRITEBYTECODE=1 /opt/homebrew/bin/python3.13 -m unittest discover \
  -s formal/tools -p test_circuit_mutations.py -v
```

The runner refuses to overwrite a completed evidence directory. It creates all
source copies and compiler outputs beneath `/private/tmp`, without modifying
the canonical source, parser, R1CS, or keys. No setup ceremony is run. The six
validator tests also exercise altered statement coordinates, invalid equations,
duplicate/noncanonical coefficients, malformed WTNS, and mutation-site guards.

## Preserved evidence and boundary

`provenance.json` records the revision, exact source/lock/reference/compiler and
library hashes, package versions, runtime versions, and temporary directory.
`results.json` contains the full commands, return codes, hashes, and results.
Each case directory has its decimal input, exact source patch, compiler and
checker logs, original rejection log where applicable, and `result.json`.
`artifacts.tar.gz` preserves the exact source, R1CS, WTNS, symbols, and WASM
bytes. Raw R1CS and witness hashes are recorded separately from the archive hash.

The original parser's allowance for the exact pinned compiler section-count
defect remains unchanged. Mutants are decoded by the lockfile-pinned `r1csfile`
0.0.48. Python separately decodes the WTNS bytes, checks canonical field values
and wire zero, and evaluates every decoded R1CS equation. The two arithmetic
checks use different field implementations; their R1CS decoding shares the
`r1csfile` dependency, so this is not an independently verified binary parser.

These are executable, complete-witness counterexamples for the four concrete
compiled mutants. They are not Lean proofs of the mutated circuits, a formal
compiler proof, Groth16 proofs under newly generated keys, or completion of the
remaining chain/refinement obligations. The original C1/C1c and W1 proofs are
separate artifacts.
