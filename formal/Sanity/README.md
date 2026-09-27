# Sanity checks on the specification

Proofs, written during review, that parts of `Spec/` mean what they should.
They are not proofs of the claims. Each Lean file imports `Spec` and depends
only on Lean's standard axioms; `lake build` checks them with the
specification. `c6consts.py` is a separate Python check that `lake build` does
not run.

| File | What it shows |
|---|---|
| `TreeLemma.lean` | `MR (L.getD i 0) i (siblingsOf L i) = TR L` for `i < 2^20`, which spendability's R3 needs |
| `Capacity.lean` | every epoch holds at most `CAPACITY` leaves in every model run |
| `SpendableR.lean` | the canonical spend satisfies `R` from the facts spendability's proof can obtain |
| `C4Sinks.lean` | C4's sink checks follow from `R` and a collision among queries the trace holds |
| `C6Proof.lean` | C6's insertion conjunct follows from its constants conjunct |
| `c6consts.py` | C6's constants conjunct, checked against `reference/poseidon_bn254.py` |
| `History.lean` | `historyEvents` of a valid write log is a model run ending at the deployment slot |
| `Mono.lean` | the trace, and so every bad event, only grows along a run |
| `C9Guard.lean` | with C9, an approved spend's proof is 256 bytes that `Groth16Accepts`, which P3 needs |
