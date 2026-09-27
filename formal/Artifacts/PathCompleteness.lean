import Artifacts.PathGates
import Proofs.CircuitCompleteness

/-! Explicit witnesses for the 40 path bits and 80 selector wires. The path
states remain ambient semantic values, so hash-gadget recovery can fill its
disjoint wire sets. No R1CS satisfaction premise is used. -/

namespace MSP.Artifacts.PathCompleteness

open PathGatesData MSP.CircuitCompleteness

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact natural reconstruction from canonical digits, independently of gates. -/
theorem index_eq_of_bits (a : Assignment) (k : Fin 2) (index : ℕ)
    (hindex : index < 2^DEPTH)
    (hbits : ∀ i < DEPTH, a (PathBitsData.bitStart k + i) = bitDigit index i) :
    PathBits.index a k = index := by
  rw [PathBits.index, PathBits.bits_eq]
  have heq : (List.range DEPTH).map (fun i => a (PathBitsData.bitStart k + i)) =
      canonicalBits DEPTH index := by
    apply List.map_congr_left
    intro i hi
    exact hbits i (List.mem_range.mp hi)
  rw [heq]
  exact canonicalBits_value DEPTH index hindex

/-- The three disjoint intervals contain 40 bits and 80 selector operands. -/
def writeSet : Finset ℕ :=
  Finset.Ico 52 92 ∪ Finset.Ico 730 770 ∪ Finset.Ico 7060 7100

theorem writeSet_card : writeSet.card = 120 := by decide

def complete (a : Assignment) (indices : Fin 2 → ℕ) : Assignment := fun wire =>
  if 52 ≤ wire ∧ wire < 72 then bitDigit (indices 0) (wire - 52) else
  if 72 ≤ wire ∧ wire < 92 then bitDigit (indices 1) (wire - 72) else
  if 730 ≤ wire ∧ wire < 750 then
    if (indices 0).testBit (wire - 730) then a (12 + (wire - 730)) else a (770 + (wire - 730)) else
  if 750 ≤ wire ∧ wire < 770 then
    if (indices 0).testBit (wire - 750) then a (770 + (wire - 750)) else a (12 + (wire - 750)) else
  if 7060 ≤ wire ∧ wire < 7080 then
    if (indices 1).testBit (wire - 7060) then a (32 + (wire - 7060)) else a (7100 + (wire - 7060)) else
  if 7080 ≤ wire ∧ wire < 7100 then
    if (indices 1).testBit (wire - 7080) then a (7100 + (wire - 7080)) else a (32 + (wire - 7080)) else
  a wire

theorem complete_preserves (a : Assignment) (indices : Fin 2 → ℕ) (wire : ℕ)
    (h : wire ∉ writeSet) : complete a indices wire = a wire := by
  simp only [writeSet, Finset.mem_union, Finset.mem_Ico] at h
  simp only [complete]
  split_ifs <;> first | omega | rfl

theorem complete_bit (a : Assignment) (indices : Fin 2 → ℕ) (k : Fin 2)
    (i : ℕ) (hi : i < DEPTH) :
    complete a indices (PathBitsData.bitStart k + i) = bitDigit (indices k) i := by
  change i < 20 at hi
  fin_cases k <;> interval_cases i <;> simp [complete, PathBitsData.bitStart]

theorem complete_cur (a : Assignment) (indices : Fin 2 → ℕ) (k : Fin 2)
    (i : ℕ) (hi : i ≤ DEPTH) :
    complete a indices (curStart k + i) = a (curStart k + i) := by
  apply complete_preserves
  change i ≤ 20 at hi
  fin_cases k <;> interval_cases i <;> decide

theorem complete_sibling (a : Assignment) (indices : Fin 2 → ℕ)
    (k : Fin 2) (l : Fin DEPTH) :
    complete a indices (PathBitsData.siblingWire k l) = a (PathBitsData.siblingWire k l) := by
  apply complete_preserves
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;> decide

theorem complete_left (a : Assignment) (indices : Fin 2 → ℕ)
    (k : Fin 2) (l : Fin DEPTH) :
    complete a indices (leftStart k + l.val) =
      if (indices k).testBit l.val then a (PathBitsData.siblingWire k l)
      else a (curStart k + l.val) := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    simp [complete, leftStart, curStart, PathBitsData.siblingWire] <;> rfl

theorem complete_right (a : Assignment) (indices : Fin 2 → ℕ)
    (k : Fin 2) (l : Fin DEPTH) :
    complete a indices (rightStart k + l.val) =
      if (indices k).testBit l.val then a (curStart k + l.val)
      else a (PathBitsData.siblingWire k l) := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;>
    simp [complete, rightStart, curStart, PathBitsData.siblingWire] <;> rfl

theorem complete_index (a : Assignment) (indices : Fin 2 → ℕ) (k : Fin 2)
    (hindex : indices k < 2^DEPTH) : PathBits.index (complete a indices) k = indices k :=
  index_eq_of_bits (complete a indices) k (indices k) hindex (complete_bit a indices k)

#print axioms complete_index

end MSP.Artifacts.PathCompleteness
