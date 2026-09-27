import Artifacts.PathCompleteness

/-! Completeness of the actual path gates. Ambient cur wires may be filled with
canonical Merkle trace values by the separate hash recovery construction. -/

namespace MSP.Artifacts.PathCompleteness

open PathGatesData MSP.CircuitCompleteness

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem neg_one :
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 : F) = -1 :=
  RangeGate.coefficient_neg_one

/-- A generic algebraic reading of every pinned left selector. -/
theorem left_holds_iff (a : Assignment) (k : Fin 2) (l : Fin DEPTH) :
    (leftConstraint k l).Holds a ↔
      (a (curStart k + l.val) - a (PathBitsData.siblingWire k l)) *
        a (PathBitsData.bitStart k + l.val) =
          a (curStart k + l.val) - a (leftStart k + l.val) := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    simp [leftConstraint, curStart, leftStart, PathBitsData.siblingWire,
      PathBitsData.bitStart, Constraint.Holds, LinearCombination.eval,
      neg_one, sub_eq_add_neg, add_comm]

theorem right_holds_iff (a : Assignment) (k : Fin 2) (l : Fin DEPTH) :
    (rightConstraint k l).Holds a ↔
      (a (PathBitsData.siblingWire k l) - a (curStart k + l.val)) *
        a (PathBitsData.bitStart k + l.val) =
          a (PathBitsData.siblingWire k l) - a (rightStart k + l.val) := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    simp [rightConstraint, curStart, rightStart, PathBitsData.siblingWire,
      PathBitsData.bitStart, Constraint.Holds, LinearCombination.eval,
      neg_one, sub_eq_add_neg, add_comm]

theorem root_holds_iff (a : Assignment) (k : Fin 2) :
    (rootConstraint k).Holds a ↔
      (a (curStart k + DEPTH) - a 4) * a (PathBitsData.valueWire k) = 0 := by
  fin_cases k <;> simp [rootConstraint, curStart, PathBitsData.valueWire,
    Constraint.Holds, LinearCombination.eval, neg_one, sub_eq_add_neg, add_comm, DEPTH]

/-- The list decomposition itself is checked against the literal artifact. -/
theorem selectors_root_list (k : Fin 2) :
    PathGatesData.constraints k =
      ((List.finRange DEPTH).flatMap fun l => [leftConstraint k l, rightConstraint k l]) ++
        [rootConstraint k] := by
  fin_cases k <;> rfl

theorem bits_list (k : Fin 2) :
    PathBitsData.constraints k =
      (List.range DEPTH).map (RangeGate.lowConstraint (PathBitsData.bitStart k)) := by
  fin_cases k <;> rfl

theorem left_complete (a : Assignment) (indices : Fin 2 → ℕ)
    (k : Fin 2) (l : Fin DEPTH) : (leftConstraint k l).Holds (complete a indices) := by
  rw [left_holds_iff, complete_cur a indices k l.val (Nat.le_of_lt l.isLt),
    complete_sibling, complete_bit a indices k l.val l.isLt, complete_left,
    bitDigit_eq]
  cases h : (indices k).testBit l.val <;> simp

theorem right_complete (a : Assignment) (indices : Fin 2 → ℕ)
    (k : Fin 2) (l : Fin DEPTH) : (rightConstraint k l).Holds (complete a indices) := by
  rw [right_holds_iff, complete_cur a indices k l.val (Nat.le_of_lt l.isLt),
    complete_sibling, complete_bit a indices k l.val l.isLt, complete_right,
    bitDigit_eq]
  cases h : (indices k).testBit l.val <;> simp

theorem bits_complete (a : Assignment) (indices : Fin 2 → ℕ) (hzero : a 0 = 1)
    (k : Fin 2) : ∀ c ∈ PathBitsData.constraints k, c.Holds (complete a indices) := by
  rw [bits_list]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hbit := bitDigit_boolean (indices k) i
  have hz : complete a indices 0 = 1 := by simpa [complete] using hzero
  simp only [RangeGate.lowConstraint, Constraint.Holds, LinearCombination.eval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one,
    one_mul, add_zero, RangeGate.coefficient_neg_one, hz, mul_one,
    complete_bit a indices k i (List.mem_range.mp hi)]
  linear_combination hbit

theorem root_complete (a : Assignment) (indices : Fin 2 → ℕ) (k : Fin 2)
    (hroot : a (PathBitsData.valueWire k) ≠ 0 → a (curStart k + DEPTH) = a 4) :
    (rootConstraint k).Holds (complete a indices) := by
  rw [root_holds_iff, complete_cur a indices k DEPTH le_rfl,
    complete_preserves a indices 4 (by decide),
    complete_preserves a indices (PathBitsData.valueWire k)
      (by fin_cases k <;> decide)]
  by_cases hz : a (PathBitsData.valueWire k) = 0
  · simp [hz]
  · simp [hroot hz]

/-- Eighty selector gates and both gated-root constraints, with their actual
ambient root values supplied by the canonical path calculation. -/
theorem selectors_roots_complete (a : Assignment) (indices : Fin 2 → ℕ)
    (k : Fin 2)
    (hroot : a (PathBitsData.valueWire k) ≠ 0 → a (curStart k + DEPTH) = a 4) :
    ∀ c ∈ PathGatesData.constraints k, c.Holds (complete a indices) := by
  rw [selectors_root_list]
  intro c hc
  rcases List.mem_append.mp hc with hm | hr
  · obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact left_complete a indices k l
    · exact right_complete a indices k l
  · have he := List.mem_singleton.mp hr
    subst c
    exact root_complete a indices k hroot


/-- Canonical intermediate values of the Merkle calculation. -/
def trace (leaf : F) (index : ℕ) (siblings : Fin DEPTH → F) (n : ℕ) : F :=
  (List.range n).foldl
    (fun cur i => if hi : i < DEPTH then
      if index.testBit i then H2 (siblings ⟨i, hi⟩) cur else H2 cur (siblings ⟨i, hi⟩)
      else cur) leaf

@[simp] theorem trace_zero (leaf : F) (index : ℕ) (siblings : Fin DEPTH → F) :
    trace leaf index siblings 0 = leaf := rfl

theorem trace_succ (leaf : F) (index : ℕ) (siblings : Fin DEPTH → F)
    (n : ℕ) (hn : n < DEPTH) :
    trace leaf index siblings (n + 1) =
      if index.testBit n then H2 (siblings ⟨n, hn⟩) (trace leaf index siblings n)
      else H2 (trace leaf index siblings n) (siblings ⟨n, hn⟩) := by
  simp only [trace, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, dite_eq_left hn]

theorem trace_end (leaf : F) (index : ℕ) (siblings : Fin DEPTH → F) :
    trace leaf index siblings DEPTH = MR leaf index siblings := by
  have hrange : List.range DEPTH = (List.finRange DEPTH).map Fin.val := by decide
  rw [trace, hrange, List.foldl_map, MR]
  congr 1
  funext cur l
  simp only [dite_eq_left l.isLt]

/-- The complete pinned path fragment contains 122 constraints. -/
def constraints : List Constraint :=
  (PathBitsData.constraints 0 ++ PathGatesData.constraints 0) ++
  (PathBitsData.constraints 1 ++ PathGatesData.constraints 1)

theorem constraints_length : constraints.length = 122 := rfl

theorem constraints_eq_slices : constraints =
    (Spend.group2.drop 124).take 61 ++ (Spend.group27.drop 76).take 61 := rfl

theorem constraints_mem {c : Constraint} (hc : c ∈ constraints) :
    c ∈ Spend.system.constraints := by
  rw [constraints_eq_slices] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact List.mem_flatten.mpr
      ⟨Spend.group2, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
  · exact List.mem_flatten.mpr
      ⟨Spend.group27, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

/-- All actual Boolean, selector, and root gates hold from their canonical
input values and root equation. It is sufficient to require membership for
nonzero inputs, exactly as R3 does. -/
theorem complete_holds_of_MR (a : Assignment) (indices : Fin 2 → ℕ)
    (leaves : Fin 2 → F) (siblings : Fin 2 → Fin DEPTH → F) (hzero : a 0 = 1)
    (hcur : ∀ k, a (curStart k + DEPTH) = MR (leaves k) (indices k) (siblings k))
    (hMR : ∀ k, a (PathBitsData.valueWire k) ≠ 0 →
      MR (leaves k) (indices k) (siblings k) = a 4) :
    ∀ c ∈ constraints, c.Holds (complete a indices) := by
  have hr (k : Fin 2) :
      a (PathBitsData.valueWire k) ≠ 0 → a (curStart k + DEPTH) = a 4 :=
    fun hv => (hcur k).trans (hMR k hv)
  intro c hc
  simp only [constraints, List.mem_append] at hc
  rcases hc with (hc | hc) | (hc | hc)
  · exact bits_complete a indices hzero 0 c hc
  · exact selectors_roots_complete a indices 0 (hr 0) c hc
  · exact bits_complete a indices hzero 1 c hc
  · exact selectors_roots_complete a indices 1 (hr 1) c hc

/-- Ambient trace values also agree with every selected hash input/output.
This is a semantic compatibility proof for the separate hash witness recovery. -/
theorem node_hashes_of_trace (a : Assignment) (indices : Fin 2 → ℕ)
    (leaves : Fin 2 → F) (siblings : Fin 2 → Fin DEPTH → F)
    (hcur : ∀ k n, n ≤ DEPTH → a (curStart k + n) = trace (leaves k) (indices k) (siblings k) n)
    (hsib : ∀ k l, a (PathBitsData.siblingWire k l) = siblings k l) :
    ∀ k, PathGates.NodeHashes (complete a indices) k := by
  intro k l
  rw [complete_cur a indices k (l.val + 1) (by omega),
    complete_left, complete_right, hcur k (l.val + 1) (by omega),
    hcur k l.val (Nat.le_of_lt l.isLt), hsib k l, trace_succ _ _ _ l.val l.isLt]
  cases (indices k).testBit l.val <;> rfl

/-- End-to-end path-fragment construction from bounded canonical indices,
semantic ambient nodes, and R3. No path constraint is assumed satisfied. -/
theorem complete_path (a : Assignment) (indices : Fin 2 → ℕ)
    (leaves : Fin 2 → F) (siblings : Fin 2 → Fin DEPTH → F) (hzero : a 0 = 1)
    (hindex : ∀ k, indices k < 2^DEPTH)
    (hcur : ∀ k n, n ≤ DEPTH → a (curStart k + n) = trace (leaves k) (indices k) (siblings k) n)
    (hsib : ∀ k l, a (PathBitsData.siblingWire k l) = siblings k l)
    (hMR : ∀ k, a (PathBitsData.valueWire k) ≠ 0 →
      MR (leaves k) (indices k) (siblings k) = a 4) :
    (∀ k, PathBits.index (complete a indices) k = indices k) ∧
    (∀ c ∈ constraints, c.Holds (complete a indices)) ∧
    (∀ k, PathGates.NodeHashes (complete a indices) k) := by
  refine ⟨fun k => complete_index a indices k (hindex k), ?_,
    node_hashes_of_trace a indices leaves siblings hcur hsib⟩
  apply complete_holds_of_MR a indices leaves siblings hzero
    (fun k => (hcur k DEPTH le_rfl).trans (trace_end _ _ _)) hMR

#print axioms complete_preserves
#print axioms constraints_mem
#print axioms complete_holds_of_MR
#print axioms complete_path

end MSP.Artifacts.PathCompleteness
