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

Still to prove in the model half: C4, C5b, C5c, C5g, C5h and spendability.
