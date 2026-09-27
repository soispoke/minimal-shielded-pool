import Proofs.NonVacuityFixtureComplete
import Proofs.NonVacuityFixtureTableCombined
import Proofs.NonVacuityFixtureTreeSupport
import Proofs.NonVacuityFixtureNoteSupport
import Proofs.NonVacuityFixturePathSupport
import Proofs.NonVacuityKeccakBindings

namespace MSP.NonVacuity

theorem fixtureTable_of_poseidon (q : Query) (h : ∃ n, (q, n) ∈ poseidonTable) :
    ∃ n, (q, n) ∈ fixtureTable := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, List.mem_append_left _ hn⟩

theorem fixtureTable_of_poseidon_map (q : Query) (h : q ∈ poseidonTable.map Prod.fst) :
    ∃ n, (q, n) ∈ fixtureTable := by
  obtain ⟨⟨q', n⟩, hn, he⟩ := List.mem_map.mp h
  cases he
  exact fixtureTable_of_poseidon q' ⟨n, hn⟩

theorem fixtureTable_of_keccak (q : Query) (h : q ∈ fixtureKeccakQueries) :
    ∃ n, (q, n) ∈ fixtureTable := by
  obtain ⟨n, hn⟩ := fixtureKeccakTable_support q h
  exact ⟨n, List.mem_append_right _ hn⟩

theorem fixture_witness_supported (q : Query)
    (hq : q ∈ witnessQueries fixtureStatement fixtureWitness) :
    ∃ n, (q, n) ∈ fixtureTable := by
  rcases fixture_witness_queries_cases q hq with ⟨k, hk⟩ | ho | ⟨k, hp⟩
  · exact fixtureTable_of_poseidon_map q (fixture_inputs_queries_supported k q hk)
  · exact fixtureTable_of_poseidon_map q (fixture_outputs_queries_supported q ho)
  · exact fixtureTable_of_poseidon q (fixture_path_support k q hp)

/-- Every query of the actual encoded execution is covered, including both
paths, the dummy path, all historical tree prefixes, storage and nonce hashes. -/
theorem fixtureTable_covers : ∀ q ∈ fixtureQueries, ∃ n, (q, n) ∈ fixtureTable := by
  simp only [fixtureQueries, List.forall_mem_append]
  repeat' apply And.intro
  · intro q hq
    exact fixtureTable_of_poseidon_map q (fixture_sink_queries_supported q hq)
  · intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact fixtureTable_of_poseidon_map _ fixture_shield_query_supported
  · exact fixture_witness_supported
  · intro q hq
    apply fixtureTable_of_keccak q
    simp only [fixtureKeccakQueries, List.mem_cons, List.not_mem_nil, or_false] at *
    tauto
  · intro q hq
    apply fixtureTable_of_keccak q
    simp only [List.mem_singleton] at hq
    subst q
    simp [fixtureKeccakQueries]
  · intro q hq
    apply fixtureTable_of_keccak q
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [fixtureKeccakQueries]
  · intro q hq
    apply fixtureTable_of_keccak q
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [fixtureKeccakQueries]
  · intro q hq
    exact fixtureTable_of_poseidon_map q (fixture_empty_queries_supported q hq)
  · intro q hq
    exact fixtureTable_of_poseidon_map q (fixture_singleton_queries_supported q hq)

end MSP.NonVacuity

namespace MSP

/-- W1 for the concrete Poseidon/Keccak model and pinned R1CS. The witness
shields two units, publishes its root, advances one slot, then spends with one
unit credited for withdrawal and one paid as gas. Every bad-event query is numerically checked. -/
theorem w1 : W1 :=
  NonVacuity.fixture_w1_of_certificates NonVacuity.fixtureTable
    NonVacuity.fixtureTable_covers NonVacuity.fixtureTable_values
    NonVacuity.fixtureTable_unique NonVacuity.fixtureTable_large
    NonVacuity.fixture_leaf_ne_sink0 NonVacuity.fixture_leaf_ne_sink1
    NonVacuity.fixture_root_ne_zero NonVacuity.fixture_nullifiers_distinct
    NonVacuity.fixture_sinks_distinct NonVacuity.fixture_nf1_ne_zero NonVacuity.fixture_nf2_ne_zero

#print axioms w1

end MSP
