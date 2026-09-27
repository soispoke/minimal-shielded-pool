import Artifacts.PathGatesData
import Artifacts.PathIndex

/-!
# Merkle selector and gated membership binding

All eighty selector equations and both final root gates are checked against the
complete pinned R1CS. The remaining premises name the concrete leaf-state wire
and each node's concrete left/right/output wires, rather than assuming a Merkle
root equation. Proving these hash premises from optimized Poseidon is separate.
-/

namespace MSP.Artifacts.PathGates

open PathGatesData

attribute [local simp] Matrix.cons_val_zero' Matrix.cons_val_succ'

private theorem neg_one :
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 : F) = -1 :=
  RangeGate.coefficient_neg_one

theorem path0_eq_slice : path0Constraints = (Spend.group2.drop 144).take 41 := rfl
theorem path1_eq_slice : path1Constraints = (Spend.group27.drop 96).take 41 := rfl

private theorem constraint_mem (k : Fin 2) {c : Constraint}
    (hc : c ∈ constraints k) : c ∈ Spend.system.constraints := by
  fin_cases k
  · change c ∈ path0Constraints at hc
    rw [path0_eq_slice] at hc
    exact List.mem_flatten.mpr
      ⟨Spend.group2, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
  · change c ∈ path1Constraints at hc
    rw [path1_eq_slice] at hc
    exact List.mem_flatten.mpr
      ⟨Spend.group27, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem left_mem (k : Fin 2) (l : Fin DEPTH) :
    leftConstraint k l ∈ Spend.system.constraints := by
  apply constraint_mem k
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    (dsimp [leftConstraint, constraints, path0Constraints, path1Constraints]; simp)

private theorem right_mem (k : Fin 2) (l : Fin DEPTH) :
    rightConstraint k l ∈ Spend.system.constraints := by
  apply constraint_mem k
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    (dsimp [rightConstraint, constraints, path0Constraints, path1Constraints]; simp)

private theorem root_mem (k : Fin 2) : rootConstraint k ∈ Spend.system.constraints := by
  apply constraint_mem k
  fin_cases k <;> simp [rootConstraint, constraints, path0Constraints, path1Constraints]

/-- The left selector equation with its exact raw operands. -/
theorem left_equation (a : Assignment) (h : Spend.system.Satisfied a)
    (k : Fin 2) (l : Fin DEPTH) :
    (a (curStart k + l.val) - (ConcreteWitness.ofAssignment a).sib k l) *
      a (PathBitsData.bitStart k + l.val) =
      a (curStart k + l.val) - a (leftStart k + l.val) := by
  have hc := h.2 _ (left_mem k l)
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    (dsimp [leftConstraint, curStart, leftStart, ConcreteWitness.ofAssignment,
      PathBitsData.siblingWire, PathBitsData.bitStart, Constraint.Holds,
      LinearCombination.eval] at hc ⊢
     simpa [neg_one, sub_eq_add_neg, add_comm] using hc)

/-- The right selector equation with its exact raw operands. -/
theorem right_equation (a : Assignment) (h : Spend.system.Satisfied a)
    (k : Fin 2) (l : Fin DEPTH) :
    ((ConcreteWitness.ofAssignment a).sib k l - a (curStart k + l.val)) *
      a (PathBitsData.bitStart k + l.val) =
      (ConcreteWitness.ofAssignment a).sib k l - a (rightStart k + l.val) := by
  have hc := h.2 _ (right_mem k l)
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    (dsimp [rightConstraint, curStart, rightStart, ConcreteWitness.ofAssignment,
      PathBitsData.siblingWire, PathBitsData.bitStart, Constraint.Holds,
      LinearCombination.eval] at hc ⊢
     simpa [neg_one, sub_eq_add_neg, add_comm] using hc)

/-- Boolean selection puts the running node right exactly at a one bit. -/
theorem selectors (a : Assignment) (h : Spend.system.Satisfied a)
    (k : Fin 2) (l : Fin DEPTH) :
    a (leftStart k + l.val) =
      (if ((ConcreteWitness.ofAssignment a).idx k).testBit l.val
       then (ConcreteWitness.ofAssignment a).sib k l else a (curStart k + l.val)) ∧
    a (rightStart k + l.val) =
      (if ((ConcreteWitness.ofAssignment a).idx k).testBit l.val
       then a (curStart k + l.val) else (ConcreteWitness.ofAssignment a).sib k l) := by
  have hl := left_equation a h k l
  have hr := right_equation a h k l
  rw [PathIndex.wire_eq_testBit a h k l] at hl hr
  cases hb : ((ConcreteWitness.ofAssignment a).idx k).testBit l.val <;>
    simp only [hb, Bool.false_eq_true, ite_false, ite_true, mul_zero, mul_one] at hl hr ⊢
  all_goals
    constructor
    · linear_combination hl
    · linear_combination hr

/-- The actual final root gate, before cancellation by nonzero input value. -/
theorem gated_root (a : Assignment) (h : Spend.system.Satisfied a) (k : Fin 2) :
    (a (curStart k + DEPTH) - (ConcreteWitness.statementOf a).root) *
      (ConcreteWitness.ofAssignment a).v k = 0 := by
  have hc := h.2 _ (root_mem k)
  fin_cases k <;>
    simpa [rootConstraint, curStart, ConcreteWitness.statementOf, Compression.statement,
      ConcreteWitness.ofAssignment, PathBitsData.valueWire, Constraint.Holds,
      LinearCombination.eval, neg_one, sub_eq_add_neg, add_comm, DEPTH] using hc

/-- The remaining node binding required from the optimized hash gadgets. -/
def NodeHashes (a : Assignment) (k : Fin 2) : Prop :=
  ∀ l : Fin DEPTH, a (curStart k + (l.val + 1)) =
    H2 (a (leftStart k + l.val)) (a (rightStart k + l.val))

private def step (a : Assignment) (k : Fin 2) (cur : F) (l : Fin DEPTH) : F :=
  if ((ConcreteWitness.ofAssignment a).idx k).testBit l.val
  then H2 ((ConcreteWitness.ofAssignment a).sib k l) cur
  else H2 cur ((ConcreteWitness.ofAssignment a).sib k l)

/-- Each concrete path-state wire advances by the canonical Merkle step,
conditional only on the corresponding actual node hash binding. -/
theorem node_step (a : Assignment) (h : Spend.system.Satisfied a)
    (k : Fin 2) (hnodes : NodeHashes a k) (l : Fin DEPTH) :
    a (curStart k + (l.val + 1)) = step a k (a (curStart k + l.val)) l := by
  rw [hnodes l, (selectors a h k l).1, (selectors a h k l).2]
  unfold step
  split <;> rfl

/-- Induct along all twenty concrete node outputs to compute the canonical root. -/
theorem root_eq_MR (a : Assignment) (h : Spend.system.Satisfied a)
    (k : Fin 2) (leaf : F) (hleaf : a (curStart k) = leaf)
    (hnodes : NodeHashes a k) :
    a (curStart k + DEPTH) =
      MR leaf ((ConcreteWitness.ofAssignment a).idx k) ((ConcreteWitness.ofAssignment a).sib k) := by
  let f : F → ℕ → F := fun cur i => if hi : i < DEPTH then step a k cur ⟨i, hi⟩ else cur
  have trace (n : ℕ) (hn : n ≤ DEPTH) :
      (List.range n).foldl f (a (curStart k)) = a (curStart k + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      simpa only [f, dite_eq_left (show n < DEPTH by omega)] using
        (node_step a h k hnodes ⟨n, by omega⟩).symm
  have ht := trace DEPTH le_rfl
  have hrange : List.range DEPTH = (List.finRange DEPTH).map Fin.val := by decide
  rw [hrange, List.foldl_map] at ht
  have hf : (fun cur (l : Fin DEPTH) => f cur l.val) = step a k := by
    funext cur l
    simp only [f, dite_eq_left l.isLt]
  rw [hf, hleaf] at ht
  exact ht.symm

/-- R3 from the actual selectors/root gate, with explicit leaf and node-hash
premises. No whole-path or Merkle-root equality is assumed. -/
theorem membership_of_hashes (a : Assignment) (h : Spend.system.Satisfied a)
    (k : Fin 2)
    (hleaf : a (curStart k) = (ConcreteWitness.ofAssignment a).leaf k)
    (hnodes : NodeHashes a k)
    (hv : (ConcreteWitness.ofAssignment a).v k ≠ 0) :
    MR ((ConcreteWitness.ofAssignment a).leaf k) ((ConcreteWitness.ofAssignment a).idx k)
      ((ConcreteWitness.ofAssignment a).sib k) = (ConcreteWitness.statementOf a).root := by
  have hg := gated_root a h k
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hg).resolve_right hv)
  rw [root_eq_MR a h k _ hleaf hnodes] at heq
  exact heq

end MSP.Artifacts.PathGates
