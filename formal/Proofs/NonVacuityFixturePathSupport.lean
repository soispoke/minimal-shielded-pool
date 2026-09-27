import Proofs.NonVacuityPoseidonSteps
import Proofs.NonVacuityPoseidonPaths
import Proofs.NonVacuityPoseidonTableData
import Proofs.NonVacuityFixtureTable

/-! Both concrete W1 witness paths query only entries of the checked finite
Poseidon table. The fold is related to explicit intermediate states before
any table membership check; no whole-path hash premise is assumed. -/

namespace MSP.NonVacuity

open PoseidonFixture

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-- At index zero every level places the running node on the left. Any
sequence satisfying those individual hash steps yields this exact query list. -/
theorem pathQueries_zero_trace (values : Fin 21 → F) (siblings : Fin 20 → F)
    (steps : ∀ i : Fin 20, H2 (values i.castSucc) (siblings i) = values i.succ) :
    pathQueries (values 0) 0 siblings =
      (List.finRange 20).map (fun i => Query.h2 (values i.castSucc) (siblings i)) := by
  have s0 : H2 (values 0) (siblings 0) = values 1 := steps 0
  have s1 : H2 (values 1) (siblings 1) = values 2 := steps 1
  have s2 : H2 (values 2) (siblings 2) = values 3 := steps 2
  have s3 : H2 (values 3) (siblings 3) = values 4 := steps 3
  have s4 : H2 (values 4) (siblings 4) = values 5 := steps 4
  have s5 : H2 (values 5) (siblings 5) = values 6 := steps 5
  have s6 : H2 (values 6) (siblings 6) = values 7 := steps 6
  have s7 : H2 (values 7) (siblings 7) = values 8 := steps 7
  have s8 : H2 (values 8) (siblings 8) = values 9 := steps 8
  have s9 : H2 (values 9) (siblings 9) = values 10 := steps 9
  have s10 : H2 (values 10) (siblings 10) = values 11 := steps 10
  have s11 : H2 (values 11) (siblings 11) = values 12 := steps 11
  have s12 : H2 (values 12) (siblings 12) = values 13 := steps 12
  have s13 : H2 (values 13) (siblings 13) = values 14 := steps 13
  have s14 : H2 (values 14) (siblings 14) = values 15 := steps 14
  have s15 : H2 (values 15) (siblings 15) = values 16 := steps 15
  have s16 : H2 (values 16) (siblings 16) = values 17 := steps 16
  have s17 : H2 (values 17) (siblings 17) = values 18 := steps 17
  have s18 : H2 (values 18) (siblings 18) = values 19 := steps 18
  simp [pathQueries, DEPTH, List.finRange, List.ofFn_succ,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18]

theorem real_path_query_mem (i : Fin 20) :
    Query.h2 (realValues i.castSucc) (zeroValues i.castSucc) ∈
      poseidonTable.map Prod.fst := by
  fin_cases i <;> decide

theorem dummy_path_query_mem (i : Fin 20) :
    Query.h2 (dummyValues i.castSucc) 0 ∈ poseidonTable.map Prod.fst := by
  fin_cases i <;> decide

theorem fixture_real_path_support (q : Query)
    (hq : q ∈ pathQueries (fixtureWitness.leaf 0) (fixtureWitness.idx 0)
      (fixtureWitness.sib 0)) : q ∈ poseidonTable.map Prod.fst := by
  have hl : fixtureWitness.leaf 0 = realValues 0 := fixture_leaf_eq
  have hs : fixtureWitness.sib 0 = fun i => zeroValues i.castSucc := by
    rw [fixture_real_siblings]
    funext i
    exact zero_value i.castSucc
  change q ∈ pathQueries (fixtureWitness.leaf 0) 0 (fixtureWitness.sib 0) at hq
  rw [hl, hs] at hq
  erw [pathQueries_zero_trace realValues (fun i => zeroValues i.castSucc) real_step] at hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact real_path_query_mem i

theorem fixture_dummy_path_support (q : Query)
    (hq : q ∈ pathQueries (fixtureWitness.leaf 1) (fixtureWitness.idx 1)
      (fixtureWitness.sib 1)) : q ∈ poseidonTable.map Prod.fst := by
  have hl : fixtureWitness.leaf 1 = dummyValues 0 := fixture_dummy_leaf_eq
  change q ∈ pathQueries (fixtureWitness.leaf 1) 0 (fixtureWitness.sib 1) at hq
  rw [hl, fixture_dummy_siblings] at hq
  erw [pathQueries_zero_trace dummyValues (fun _ => 0) dummy_step] at hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact dummy_path_query_mem i

theorem fixture_path_support (k : Fin 2) (q : Query)
    (hq : q ∈ pathQueries (fixtureWitness.leaf k) (fixtureWitness.idx k)
      (fixtureWitness.sib k)) : ∃ n, (q, n) ∈ poseidonTable := by
  have hm : q ∈ poseidonTable.map Prod.fst := by
    fin_cases k
    · exact fixture_real_path_support q hq
    · exact fixture_dummy_path_support q hq
  obtain ⟨⟨r, n⟩, hp, he⟩ := List.mem_map.mp hm
  cases he
  exact ⟨n, hp⟩

#print axioms pathQueries_zero_trace
#print axioms fixture_real_path_support
#print axioms fixture_dummy_path_support
#print axioms fixture_path_support

end MSP.NonVacuity
