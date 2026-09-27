import Proofs.NonVacuityPoseidonTable
import Proofs.NonVacuityPoseidon

namespace MSP.NonVacuity

noncomputable section
open PoseidonFixture

def fixtureInputQueries (k : Fin 2) : List Query :=
  [.h3 1 (fixtureWitness.sk k) 0,
   .h2 (pk (fixtureWitness.sk k)) (fixtureWitness.ρ k),
   .h3 2 (inner (fixtureWitness.sk k) (fixtureWitness.ρ k)) (fixtureWitness.v k),
   .h2 fixtureStatement.d (fixtureWitness.sk k),
   .h2 (fixtureWitness.leaf k) (fixtureWitness.idx k : F),
   .h3 4 (nfKey fixtureStatement.d (fixtureWitness.sk k))
     (H2 (fixtureWitness.leaf k) (fixtureWitness.idx k : F))]

def fixtureOutputQueries : List Query :=
  [.h3 2 (fixtureWitness.oi 0) (fixtureWitness.ov 0),
   .h3 2 (fixtureWitness.oi 1) (fixtureWitness.ov 1)]

theorem fixture_inputs_queries_supported (k : Fin 2) :
    ∀ q ∈ fixtureInputQueries k, q ∈ poseidonTable.map Prod.fst := by
  fin_cases k
  all_goals
    simp only [fixtureInputQueries, fixtureWitness, fixtureSpend, mkSpend,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      Witness.leaf, fixtureStatement, fixtureParameters, pk, inner, cm, nfKey,
      Nat.cast_zero, domain_one_one_zero_eq,
      pk1_hash, pk2_hash, inner1_hash, inner2_hash, leaf_hash, dummyLeaf_hash,
      nfKey1_hash, nfKey2_hash, occurrence1_hash, occurrence2_hash]
    decide

theorem fixture_outputs_queries_supported :
    ∀ q ∈ fixtureOutputQueries, q ∈ poseidonTable.map Prod.fst := by
  decide

theorem fixture_sink_queries_supported :
    ∀ q ∈ [Query.h3 2 1 0, .h3 2 2 0], q ∈ poseidonTable.map Prod.fst := by
  decide

theorem fixture_shield_query_supported :
    Query.h3 2 fixtureInner 2 ∈ poseidonTable.map Prod.fst := by
  rw [fixture_inner_eq]
  decide

theorem fixture_witness_queries_cases (q : Query)
    (hq : q ∈ witnessQueries fixtureStatement fixtureWitness) :
    (∃ k, q ∈ fixtureInputQueries k) ∨ q ∈ fixtureOutputQueries ∨
      (∃ k, q ∈ pathQueries (fixtureWitness.leaf k) (fixtureWitness.idx k)
        (fixtureWitness.sib k)) := by
  simp only [witnessQueries, List.mem_append, List.mem_flatMap] at hq
  rcases hq with ⟨k, _, hk⟩ | ho
  · rcases hk with hi | hp
    · exact Or.inl ⟨k, hi⟩
    · exact Or.inr (Or.inr ⟨k, hp⟩)
  · exact Or.inr (Or.inl ho)

end
end MSP.NonVacuity
