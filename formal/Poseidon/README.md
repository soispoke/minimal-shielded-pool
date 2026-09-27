# Concrete BN254 Poseidon reference

`MSP.Poseidon.hash2`, `hash3` and `hash10` are the concrete functions used by
`Spec.Hash`'s `H2`, `H3` and `H10` definitions. They use BN254 scalar-field
arithmetic, initial state `[0, inputs...]`, the fifth-power S-box, eight full
rounds, and respectively 57, 56 and 66 partial rounds. After adding each round's
constants, full rounds apply the S-box to every element and partial rounds
apply it only to element zero. Mixing uses `new[i] = Σ_j M[i][j] * state[j]`.
The output is the final state at index zero.

`Permutation.lean` defines this schedule for any typed parameter set. Eager
vectors hold every intermediate state. `Constants.lean` supplies the three
parameter sets, with Lean checking the round-constant and matrix dimensions.
`Hash.lean` supplies the concrete arities and `zeroHash`, the recursive zero
hashes needed by C6. The definitions introduce no admissions or new axioms;
`Audit.lean` reports `[propext, Quot.sound]` for all four functions.

`generate.py` copies the committed reference constants into typed Lean vectors.
Before generating, it verifies full SHA-256 hashes of the Python reference,
constants, stored vectors, exporter, circuit source, package lock and relevant
installed circomlib sources. It checks every imported constant is below `p`,
the round schedule and dimensions, package versions, and exact numeric equality
with circomlibjs's reference constants and matrices. `manifest.json` records
the input hashes, generator hash and generated-module hash. No absolute local
paths or timestamps affect generation.

From `formal/`, after installing the repository's pinned tooling dependencies:

```sh
python3 Poseidon/generate.py --check
lake build Poseidon
python3 Poseidon/check.py
lake env lean Poseidon/Audit.lean
```

Use `generate.py` without `--check` to regenerate. Both Python commands accept
`--node-modules /path/to/tooling/node_modules`; `check.py` also accepts
`--lake /path/to/lake`. Only the installed dependencies are read from an
alternate path, never that checkout's circuit or reference source.

The differential check executes the Lean functions and the separately written
committed Python reference. Its 202 comparisons cover all 48 stored direct
vectors, 11 calls in the tagged pool chain, two sinks, 20 zero-hash steps, all
21 direct evaluations of `zeroHash` from level zero through 20, 40 incremental
tree calls, 12 modulus-boundary inputs, and 48 additional deterministic inputs.
It also checks the stored tree roots and all 21 constants used by C6. These are
executable checks. Separately, `Proofs/PoseidonConstants.lean` checks all 21
constants in Lean's kernel using ordinary `decide`, without `native_decide`.
`Proofs/C6.lean` connects them to the specified tree algorithm and proves C6.

The canonical Python reference and `circomlibjs/src/poseidon_reference.js`
use the ordinary full matrix at every round. The circuit actually included by
`spend.circom`, circomlib 2.0.5's `poseidon.circom`, uses optimized sparse rounds,
transformed constants and transposed matrix indexing. That source and its
constants are pinned here, but this module does not prove equivalence between
the optimized circuit and the reference function. It also does not prove
Poseidon security, R1CS soundness/completeness, or the EVM libraries' behavior
and gas bounds. Those remain separate bindings. `Spec.Hash` marks the concrete
hash wrappers irreducible to prevent accidental expansion during symbolic
proofs; their bodies remain available for explicit unfolding and kernel checks.
