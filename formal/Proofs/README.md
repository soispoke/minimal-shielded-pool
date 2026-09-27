# Proofs of model claims

Early proofs of claims in `Spec/`, written during review. The hashes stay
opaque: each claim is proven for every choice of `H2`, `H3`, `H10` and `K`,
ending in "or the run has a bad event" where the claim does. Each depends only
on Lean's standard axioms, and `lake build` checks them.

| File | Proves |
|---|---|
| `C5d.lean` | `C5d P` for every pool |
| `C3.lean` | `C5e P` for every pool, and `C1 → C3 P` |
| `C5a.lean` | `C1 → C5a P` |
| `C5cC4.lean` | `C1 → C5b P → C5c P`, and `C1 → C5b P → C5c P → C4 P` |
| `Path.lean` | the path walk: a Merkle path whose root is `TR L`, without a collision against `L`'s tree queries, starts at `L`'s leaf |
| `C5i.lean` | `C5b P → C5i P` |
| `C5b.lean` | `C1 → C5b P` |
| `Model.lean` | `C1 → C5g P`, `C1 → C5h P`, `C1 → Spendable P`, and `model_theorem_of`: `ModelTheorem` given C5j and C5k |

Every model claim is proven from C1 except C5j and C5k, added after the others
to state what deposits, settlements and publication must do; their proofs are
pending. What else remains: C1 and C1c against the constraint system (step 3),
the chain half (step 5), `Composes`, and the non-vacuity witnesses `W1` (needs
concrete hashes) and `W2` (needs the EVM semantics).
