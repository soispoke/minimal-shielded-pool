import Artifacts.Witness
import Mathlib.Data.Nat.Bits

/-!
# Raw path bits and the canonical Merkle index

The forty pinned Boolean constraints make each private bit equal the digit
selected by `MR` from the reconstructed natural index. This proves digit order;
the actual circuit's mux equations and Poseidon gadgets remain separate.
-/

namespace MSP.Artifacts.PathIndex

/-- Recover a Boolean field digit from its little-endian natural encoding. -/
theorem bitsValue_testBit (bs : List F)
    (hb : ∀ b ∈ bs, b * (b - 1) = 0) (i : ℕ) (hi : i < bs.length) :
    (if (MSP.bitsValue bs).testBit i then (1 : F) else 0) = bs[i] := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    have htail : ∀ c ∈ bs, c * (c - 1) = 0 :=
      fun c hc => hb c (List.mem_cons_of_mem b hc)
    have hdigit := (MSP.boolean_constraint b).mp (hb b (by simp))
    have hencode : MSP.bitsValue (b :: bs) =
        Nat.bit (decide (b = 1)) (MSP.bitsValue bs) := by
      rcases hdigit with rfl | rfl
      · simp [MSP.bitsValue, Nat.bit]
      · have hone : (1 : F).val = 1 := by
          change 1 % p = 1
          norm_num [p]
        simp [MSP.bitsValue, Nat.bit, hone, Nat.add_comm]
    rw [hencode]
    cases i with
    | zero =>
      rw [Nat.testBit_bit_zero]
      rcases hdigit with rfl | rfl <;> simp
    | succ i =>
      rw [Nat.testBit_bit_succ]
      exact ih htail i (Nat.lt_of_succ_lt_succ hi)

/-- The exact raw private path-bit wire is the digit used by canonical `MR`. -/
theorem wire_eq_testBit (w : Assignment) (h : Spend.system.Satisfied w)
    (k : Fin 2) (l : Fin DEPTH) :
    w (PathBitsData.bitStart k + l.val) =
      if ((ConcreteWitness.ofAssignment w).idx k).testBit l.val then (1 : F) else 0 := by
  have hb : ∀ b ∈ PathBits.bits w k, b * (b - 1) = 0 := by
    intro b hb
    rw [PathBits.bits_eq] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact PathBits.bit_boolean w h k i (List.mem_range.mp hi)
  have hl : l.val < (PathBits.bits w k).length := by
    simpa only [PathBits.bits_eq, List.length_map, List.length_range] using l.isLt
  have hdigit := bitsValue_testBit (PathBits.bits w k) hb l.val hl
  change w (PathBitsData.bitStart k + l.val) =
    if (MSP.bitsValue (PathBits.bits w k)).testBit l.val then (1 : F) else 0
  simpa only [PathBits.bits_eq, List.getElem_map, List.getElem_range] using hdigit.symm

/-- A selector is true exactly when the corresponding actual bit wire is one. -/
theorem testBit_true_iff (w : Assignment) (h : Spend.system.Satisfied w)
    (k : Fin 2) (l : Fin DEPTH) :
    ((ConcreteWitness.ofAssignment w).idx k).testBit l.val = true ↔
      w (PathBitsData.bitStart k + l.val) = 1 := by
  rw [wire_eq_testBit w h k l]
  cases ((ConcreteWitness.ofAssignment w).idx k).testBit l.val <;> simp

/-- The canonical Merkle fold uses the same orientation as the raw bit wires.
This is a statement about `MR`; the circuit's mux recurrence is `PathGates.root_eq_MR`. -/
theorem MR_eq_raw_fold (w : Assignment) (h : Spend.system.Satisfied w)
    (k : Fin 2) (leaf : F) :
    MR leaf ((ConcreteWitness.ofAssignment w).idx k) ((ConcreteWitness.ofAssignment w).sib k) =
      (List.finRange DEPTH).foldl
        (fun cur l => if w (PathBitsData.bitStart k + l.val) = 1
          then H2 ((ConcreteWitness.ofAssignment w).sib k l) cur
          else H2 cur ((ConcreteWitness.ofAssignment w).sib k l)) leaf := by
  unfold MR
  congr 1
  funext cur l
  simp only [testBit_true_iff w h k l]

end MSP.Artifacts.PathIndex
