# Pinned R1CS extraction

This is the first concrete artifact-binding step. The extractor checks every
constraint and wire label in the pinned `build/spend.r1cs`, reproduces the exact
binary and symbol file with the pinned compiler, and exports the constraints as
Lean data interpreted by `R1CS.lean`. It does **not** prove C1 or C1c or replace
`Spec.Circuit`'s opaque declarations.

The full artifact SHA-256 is
`e2f6fc89bc0e478231935d7dab10fb07316f2c6dab4303e95da1a390ce84f9bf`.
There are 14,802 constraints, 185,677 terms, 14,842 wires and 46,772 labels.
`spend.manifest.json` records the field, counts, section offsets and hashes,
source and toolchain-lock hashes, exact symbol-file hash, and the statement,
public and private signal rows. JSON `null` means that optimization eliminated
the signal's wire. It is never silently mapped to wire zero.

## Reproduce and check

From the repository root, with the lockfile dependencies installed using
`npm ci --prefix tooling`:

```sh
python3 formal/tools/r1cs_artifact.py
python3 formal/tools/r1cs_artifact.py --reproduce tooling/node_modules
python3 -m unittest discover -s formal/tools -p 'test_*.py' -v
node formal/tools/crosscheck_r1cs.cjs tooling/node_modules build/spend.r1cs formal/Artifacts/spend.manifest.json
```

`--reproduce` invokes only the compiler, in a fresh temporary directory. It does
not rerun the setup ceremony or overwrite `build/`. It checks circom2 0.2.8 and
circomlib 2.0.5, the committed source and lockfile hashes, then requires the full
R1CS digest and symbol-file digest to match. Every surviving symbol's label is
checked against the R1CS wire-to-label section, including all non-public wires.
The public wires are checked to be `(beta, gamma, alpha)` at indices `(1, 2, 3)`.
The dependency package versions alone are not an integrity check of an installed
`node_modules`; byte-for-byte compiler output and the pinned symbol digest are
the acceptance gates. The Python extractor and compiler-to-symbol association
remain an external, audited part of the binding, not kernel-verified parsers.

The independent check uses lockfile-pinned `r1csfile` 0.0.48 with integer field
arithmetic and compares every decoded constraint coefficient and wire label via
canonical hashes. Its decimal constraint stream is one `A;B;C` line per
constraint, with each side a comma-separated list of `wire:coefficient` pairs
sorted by wire. Constraint order, sides, zero coefficients and all terms are
retained. The Lean export preserves the original term order as well.

The first reproduction on 2026-09-27 used the matching dependencies already at
`/Volumes/PrivateAI/WorkRepos/minimal-shielded-pool/tooling/node_modules`; that
checkout's circuit source was not used. Passing that absolute directory to
`--reproduce` and the cross-check works without copying dependencies into this
checkout. The exact reproduced symbol digest is
`10342e79bcec6e19ff64cb1ae34b433ab1780f926686e08828af1af78b1115f7`.

`Spend.lean` contains the complete generated constraint data and is kept in the
proof repository because `FullCompression` proves against that exact system.
Check byte-for-byte regeneration from the source binary:

```sh
python3 formal/tools/r1cs_artifact.py --check-lean formal/Artifacts/Spend.lean
cd formal
lake build Artifacts.FullCompression
```

To explicitly regenerate the file from the repository root:

```sh
python3 formal/tools/r1cs_artifact.py --export-lean formal/Artifacts/Spend.lean
```

The exporter uses eight-constraint definitions and grouped concatenation to
keep Lean elaboration depth bounded. The complete generated file typechecked
on 2026-09-27 with `lake env lean`, as did `lake build Artifacts`. All ten
extractor Python tests, exact circuit recompilation and the independent decoder check
also passed. `#print axioms` for the four semantic lemmas lists only `propext`
and `Quot.sound`, with no admissions.
`MSP.Artifacts.System.Satisfied` states only wire zero equals one and each
constraint's `A(w) * B(w) = C(w)`. Its coefficient field is exactly `MSP.F`.
The checked `satisfied_congr` theorem establishes that a well-formed system's
satisfaction depends only on its declared wires. No theorem substitutes the
high-level spend relation for this constraint relation.

## Concrete gamma proof

`CompressionData.lean` contains exact constraints 0 through 8, generated directly
from the fully pinned R1CS. Check or explicitly regenerate it from the repository
root:

```sh
python3 formal/tools/compression_fragment.py
python3 formal/tools/compression_fragment.py --write
```

`Compression.gamma_of_constraints` proves that every raw wire assignment
satisfying these actual extracted constraints has
`w[2] = γ(statement(w), w[3] + w[1])`. The statement is
`(w[99], w[100], w[101], w[102], w[4], w[5], w[96], fee, w[97], w[98])`, with
`fee = w[10] + w[11] - w[94] - w[95] - w[96]` in `F`. The proof evaluates the
actual canonical coefficients, converts `p - 1` to `-1`, and combines the nine
Horner equations to obtain the exact `Spec.Hash.γ` polynomial. It does not
assume that polynomial equation as a premise.

`gamma_of_system` lifts this result to any satisfying assignment of a system
containing those nine constraints. `FullCompression.compression_prefix_eq`
checks by definitional equality that the nine constraints are precisely the
first nine entries of `Spend.chunk0 ++ Spend.chunk1`. Membership proofs through
the generated chunks and groups establish that they occur in the complete
`Spend.system.constraints` list. `FullCompression.gamma_of_pinned_r1cs` therefore
requires only that the raw assignment satisfies the complete `Spend.system`;
it has no unproved containment premise. The byte-for-byte regeneration check
connects the full Lean data to the pinned binary outside Lean. No kernel-checked
binary parser is claimed.
The theorem does not yet show `w[1] = β(statement(w))`, agreement of the fee and
other projected values with all remaining gadgets, C1, or C1c. The code leaves
`Spec.Circuit`'s opaque definitions unchanged.

`lake build Artifacts` checks the fragment and full-system compression theorems. Their
`#print axioms` output is `[propext, Classical.choice, Quot.sound]`; there are
no admissions.
The Python test suite also checks exact fragment reproduction and rejects a
one-byte artifact mutation and a mutated generated Lean constraint.

## Exact serialization exception

The pinned binary's header declares **five** sections, but it contains exactly
**three**, in the order constraints (2), header (1), wire-to-label (3). The last
section ends exactly at byte 6,980,844. Recompiling the pinned source with
circom2 0.2.8 reproduces these bytes, including the mismatched count. The
`r1csfile` decoder used by the existing tooling reads these same constraints.
This is a format defect, not evidence of omitted circuit constraints.

The strict parser rejects the defect. The pinned-artifact entry point accepts
it only when the **entire file** has the exact full SHA-256 above and the
observed section pattern is `[2, 1, 3]`. It never repairs or rehashes the artifact.
All other structural checks still run. A one-byte mutation cannot obtain this
exception, even if it leaves the field coefficient structurally valid.

```sh
python3 formal/tools/r1cs_artifact.py --strict
# Expected exit 1: section count mismatch.
```

The parser bounds every read, consumes each section exactly, checks the BN254
modulus and canonical coefficients, checks wire bounds and duplicate terms,
rejects duplicate/unknown/custom sections and trailing bytes, and checks the
wire-to-label map. It supports arbitrary ordering of the three standard
sections. It is deliberately a strict Groth16 profile, not a general reader
for every R1CS extension. Tests include every truncation of a small valid
fixture, invalid headers/counts/sections/coefficients/maps, an excessive
allocation-count request, the pinned exception, and mutated artifact rejection.
These are decoder tests, **not** SPEC.md's required semantic circuit mutations.

## Remaining proof frontier

1. Reconstruct eliminated signals from retained wires and prove the projections
   are the ones required by `Spec.Circuit`. `main.stmt[4..9]` are eliminated, as
   is the private input `main.fee`; even the top fee range-check bit is
   eliminated. The source's conservation equation suggests reconstructing fee
   as `in_value[0] + in_value[1] - out_value[0] - out_value[1] - public_amount`
   in the field. This is a candidate projection, not a proved binding. A symbol
   hash or a source-level alias is insufficient to establish it. The first
   nine actual R1CS constraints encode the Horner chain; constraint 1 already
   contains this exact fee expression. The gamma equation for this projection
   is now proved from those actual constraints as described above. Next connect
   the same projection to the remaining gadgets and establish its beta digest.
2. Establish the complete constraints-to-semantics connection, including
   optimized Poseidon gadgets, bit decompositions, path selection, membership
   gating, sink/distinctness constraints, field-to-integer accounting and
   compression. The exported constraints are data; compiling them alone does
   not prove their equivalence to the intended circuit.
3. Instantiate `Assignment`, `Satisfied`, `stmtOf`, `witOf` and `publicOf` from
   that concrete system and prove C1 and C1c, including witness construction for
   arbitrary valid `R` and every alpha. Run SPEC.md's semantic mutation gates.
   Concrete Groth16 key/verifier and chain bindings remain separate obligations.

Keep the cryptographic and deployment premises in `SPEC.md`; these scripts
make no new claim about setup honesty, zkey consistency or spend authority.
