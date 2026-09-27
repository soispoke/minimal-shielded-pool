import Proofs.NonVacuityPoseidonTable
import Proofs.NonVacuityPoseidon

namespace MSP.NonVacuity

open PoseidonFixture

theorem emptyQueries_level (h : ℕ) (q : Query) (hq : q ∈ emptyQueries h) :
    ∃ l < h, q = .h2 (Z l) (Z l) := by
  induction h with
  | zero => simp [emptyQueries] at hq
  | succ h ih =>
    simp only [emptyQueries, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · obtain ⟨l, hl, he⟩ := ih hq
      exact ⟨l, by omega, he⟩
    · exact ⟨h, by omega, hq⟩

theorem compactQueries_singleton_step (h : ℕ) (leaf : F) :
    compactQueries (h + 1) [leaf] = compactQueries h [leaf] ++ emptyQueries h ++
      [.h2 (treeRoot h [leaf]) (Z h)] := by
  have hp : 0 < 2 ^ h := by positivity
  have ht : ([leaf] : List F).take (2 ^ h) = [leaf] := by
    apply List.take_of_length_le
    change 1 ≤ 2 ^ h
    omega
  have hd : ([leaf] : List F).drop (2 ^ h) = [] := by
    apply List.drop_eq_nil_of_le
    change 1 ≤ 2 ^ h
    omega
  change compactQueries h ([leaf].take (2 ^ h)) ++
    compactQueries h ([leaf].drop (2 ^ h)) ++
      [.h2 (compactRoot h ([leaf].take (2 ^ h)))
        (compactRoot h ([leaf].drop (2 ^ h)))] = _
  rw [ht, hd, compactQueries_nil, compactRoot_eq, compactRoot_eq, treeRoot_nil]

theorem compactQueries_singleton_level (h : ℕ) (leaf : F) (q : Query)
    (hq : q ∈ compactQueries h [leaf]) :
    (∃ l < h, q = .h2 (Z l) (Z l)) ∨
      (∃ l < h, q = .h2 (treeRoot l [leaf]) (Z l)) := by
  induction h with
  | zero => simp [compactQueries, compactTree] at hq
  | succ h ih =>
    rw [compactQueries_singleton_step] at hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | hq
    · rcases ih hq with ⟨l, hl, he⟩ | ⟨l, hl, he⟩
      · exact Or.inl ⟨l, by omega, he⟩
      · exact Or.inr ⟨l, by omega, he⟩
    · obtain ⟨l, hl, he⟩ := emptyQueries_level h q hq
      exact Or.inl ⟨l, by omega, he⟩
    · exact Or.inr ⟨h, by omega, hq⟩

theorem poseidon_zero_query_supported (i : Fin 20) :
    Query.h2 (zeroValues i.castSucc) (zeroValues i.castSucc) ∈ poseidonTable.map Prod.fst := by
  revert i
  decide

theorem poseidon_real_query_supported (i : Fin 20) :
    Query.h2 (realValues i.castSucc) (zeroValues i.castSucc) ∈ poseidonTable.map Prod.fst := by
  revert i
  decide

theorem fixture_empty_queries_supported (q : Query) (hq : q ∈ compactQueries DEPTH []) :
    q ∈ poseidonTable.map Prod.fst := by
  rw [compactQueries_nil] at hq
  obtain ⟨l, hl, rfl⟩ := emptyQueries_level DEPTH q hq
  have hi : l < 20 := hl
  rw [zero_value ⟨l, by omega⟩]
  exact poseidon_zero_query_supported ⟨l, hi⟩

theorem fixture_singleton_queries_supported (q : Query)
    (hq : q ∈ compactQueries DEPTH [fixtureLeaf]) : q ∈ poseidonTable.map Prod.fst := by
  rcases compactQueries_singleton_level DEPTH fixtureLeaf q hq with
      ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
  · have hi : l < 20 := hl
    rw [zero_value ⟨l, by omega⟩]
    exact poseidon_zero_query_supported ⟨l, hi⟩
  · have hi : l < 20 := hl
    rw [real_value ⟨l, by omega⟩, zero_value ⟨l, by omega⟩]
    exact poseidon_real_query_supported ⟨l, hi⟩

end MSP.NonVacuity
