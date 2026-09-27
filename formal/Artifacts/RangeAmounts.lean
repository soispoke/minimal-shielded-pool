import Artifacts.Range
import Artifacts.RangeAmountsData
import Artifacts.RangeGate
import Artifacts.Compression
import Proofs.CircuitArithmetic

/-!
# All six amount bounds and integer conservation

The five additional 128-bit gates below are bound to exact slices of the full
pinned constraint list. Field coefficient permutation certificates reconstruct
the eliminated high bits, including the optimized and reordered fee gate.
The fee uses the same concrete projection as the checked compression theorem.
These are circuit fragments; whole C1/C1c and statement/witness binding remain open.
-/

namespace MSP.Artifacts.RangeAmounts

open RangeAmountsData RangeGate RangeLemmas

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem checked_gate_range (w : Assignment) (h : Spend.system.Satisfied w)
    (start : ℕ) (low : List Constraint) (top : Constraint) (amount : LinearCombination)
    (hlow : low = (List.range 127).map (lowConstraint start))
    (hm : ∀ c ∈ low ++ [top], c ∈ Spend.system.constraints)
    (ha : top.a = (0, p - 1) :: top.b) (hc : top.c = [])
    (certificate :
      (top.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))).Perm
        ((amount.map fun t => (t.1, (t.2 : F))) ++
          ((weightedWires start 127).map fun t => (t.1, -(t.2 : F))))) :
    (amount.eval w).val < 2^128 := by
  apply gate128_range w h.1 start top (amount.eval w)
  · intro i hi
    apply h.2 _ (hm _ (List.mem_append_left _ ?_))
    rw [hlow]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  · exact h.2 top (hm top (List.mem_append_right _ (by simp)))
  · exact ha
  · exact hc
  · exact reconstruction_of_coefficients top.b amount start certificate w

/-- The exact generated secondInput gate's location in the complete constraint list. -/
theorem secondInput_eq_slice :
    secondInputConstraints = ((Spend.group54 ++ Spend.group55).drop 174).take 128 := rfl

private theorem secondInput_mem {c : Constraint} (hc : c ∈ secondInputConstraints) :
    c ∈ Spend.system.constraints := by
  rw [secondInput_eq_slice] at hc
  have hm := List.mem_of_mem_drop (List.mem_of_mem_take hc)
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_flatten.mpr ⟨Spend.group54, by simp, hm⟩
  · exact List.mem_flatten.mpr ⟨Spend.group55, by simp, hm⟩

private theorem secondInput_low_eq :
    secondInputLow = (List.range 127).map (lowConstraint 14045) := rfl

/-- Kernel-checked coefficient equality up to a permutation, preserving all terms. -/
private theorem secondInput_coefficients :
    (secondInputTop.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))).Perm
      ((([(11, 1)] : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 14045 127).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Range bound derived from the pinned constraints for every satisfying assignment. -/
theorem second_input_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 11).val < 2^128 := by
  have bound := checked_gate_range w h 14045 secondInputLow secondInputTop [(11, 1)]
    secondInput_low_eq (fun _ hc => secondInput_mem hc) (by rfl) (by rfl) secondInput_coefficients
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_one, one_mul, add_zero] using bound

/-- The exact generated firstOutput gate's location in the complete constraint list. -/
theorem firstOutput_eq_slice :
    firstOutputConstraints = (Spend.group55.drop 46).take 128 := rfl

private theorem firstOutput_mem {c : Constraint} (hc : c ∈ firstOutputConstraints) :
    c ∈ Spend.system.constraints := by
  rw [firstOutput_eq_slice] at hc
  exact List.mem_flatten.mpr
    ⟨Spend.group55, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem firstOutput_low_eq :
    firstOutputLow = (List.range 127).map (lowConstraint 14172) := rfl

/-- Kernel-checked coefficient equality up to a permutation, preserving all terms. -/
private theorem firstOutput_coefficients :
    (firstOutputTop.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))).Perm
      ((([(94, 1)] : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 14172 127).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Range bound derived from the pinned constraints for every satisfying assignment. -/
theorem first_output_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 94).val < 2^128 := by
  have bound := checked_gate_range w h 14172 firstOutputLow firstOutputTop [(94, 1)]
    firstOutput_low_eq (fun _ hc => firstOutput_mem hc) (by rfl) (by rfl) firstOutput_coefficients
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_one, one_mul, add_zero] using bound

/-- The exact generated secondOutput gate's location in the complete constraint list. -/
theorem secondOutput_eq_slice :
    secondOutputConstraints = ((Spend.group55 ++ Spend.group56).drop 174).take 128 := rfl

private theorem secondOutput_mem {c : Constraint} (hc : c ∈ secondOutputConstraints) :
    c ∈ Spend.system.constraints := by
  rw [secondOutput_eq_slice] at hc
  have hm := List.mem_of_mem_drop (List.mem_of_mem_take hc)
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_flatten.mpr ⟨Spend.group55, by simp, hm⟩
  · exact List.mem_flatten.mpr ⟨Spend.group56, by simp, hm⟩

private theorem secondOutput_low_eq :
    secondOutputLow = (List.range 127).map (lowConstraint 14299) := rfl

/-- Kernel-checked coefficient equality up to a permutation, preserving all terms. -/
private theorem secondOutput_coefficients :
    (secondOutputTop.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))).Perm
      ((([(95, 1)] : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 14299 127).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Range bound derived from the pinned constraints for every satisfying assignment. -/
theorem second_output_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 95).val < 2^128 := by
  have bound := checked_gate_range w h 14299 secondOutputLow secondOutputTop [(95, 1)]
    secondOutput_low_eq (fun _ hc => secondOutput_mem hc) (by rfl) (by rfl) secondOutput_coefficients
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_one, one_mul, add_zero] using bound

/-- The exact generated publicAmount gate's location in the complete constraint list. -/
theorem publicAmount_eq_slice :
    publicAmountConstraints = (Spend.group56.drop 46).take 128 := rfl

private theorem publicAmount_mem {c : Constraint} (hc : c ∈ publicAmountConstraints) :
    c ∈ Spend.system.constraints := by
  rw [publicAmount_eq_slice] at hc
  exact List.mem_flatten.mpr
    ⟨Spend.group56, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem publicAmount_low_eq :
    publicAmountLow = (List.range 127).map (lowConstraint 14426) := rfl

/-- Kernel-checked coefficient equality up to a permutation, preserving all terms. -/
private theorem publicAmount_coefficients :
    (publicAmountTop.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))).Perm
      ((([(96, 1)] : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 14426 127).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Range bound derived from the pinned constraints for every satisfying assignment. -/
theorem public_amount_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 96).val < 2^128 := by
  have bound := checked_gate_range w h 14426 publicAmountLow publicAmountTop [(96, 1)]
    publicAmount_low_eq (fun _ hc => publicAmount_mem hc) (by rfl) (by rfl) publicAmount_coefficients
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_one, one_mul, add_zero] using bound

/-- The exact generated fee gate's location in the complete constraint list. -/
theorem fee_eq_slice :
    feeConstraints = ((Spend.group56 ++ Spend.group57).drop 174).take 128 := rfl

private theorem fee_mem {c : Constraint} (hc : c ∈ feeConstraints) :
    c ∈ Spend.system.constraints := by
  rw [fee_eq_slice] at hc
  have hm := List.mem_of_mem_drop (List.mem_of_mem_take hc)
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_flatten.mpr ⟨Spend.group56, by simp, hm⟩
  · exact List.mem_flatten.mpr ⟨Spend.group57, by simp, hm⟩

/-- The fee projection also used by the concrete compression proof. The
coefficient certificate below ties it to the actual fee range constraint. -/
def feeAmount : LinearCombination :=
  [(10, 1), (11, 1), (94, p - 1), (95, p - 1), (96, p - 1)]

theorem feeAmount_eval (w : Assignment) :
    feeAmount.eval w = (Compression.statement w).fee := by
  simp only [feeAmount, LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero,
    coefficient_neg_one, Compression.statement]
  ring

private theorem fee_low_eq :
    feeLow = (List.range 127).map (lowConstraint 14553) := rfl

/-- Kernel-checked coefficient equality up to a permutation, preserving all terms. -/
private theorem fee_coefficients :
    (feeTop.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))).Perm
      (((feeAmount : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 14553 127).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Range bound derived from the pinned constraints for every satisfying assignment. -/
theorem fee_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (Compression.statement w).fee.val < 2^128 := by
  have bound := checked_gate_range w h 14553 feeLow feeTop feeAmount
    fee_low_eq (fun _ hc => fee_mem hc) (by rfl) (by rfl) fee_coefficients
  simpa only [feeAmount_eval] using bound

/-- All six concrete circuit amount projections have the required 128-bit bounds. -/
theorem all_amount_ranges (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 10).val < 2^128 ∧ (w 11).val < 2^128 ∧
    (w 94).val < 2^128 ∧ (w 95).val < 2^128 ∧
    (w 96).val < 2^128 ∧ (Compression.statement w).fee.val < 2^128 :=
  ⟨Range.first_input_range w h, second_input_range w h, first_output_range w h,
   second_output_range w h, public_amount_range w h, fee_range w h⟩

/-- The optimized fee projection satisfies conservation over the integers;
the six actual range gates rule out modular wraparound. -/
theorem integer_conservation (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 10).val + (w 11).val =
      (w 94).val + (w 95).val + (w 96).val + (Compression.statement w).fee.val := by
  apply (MSP.value_conservation_iff (w 10) (w 11) (w 94) (w 95) (w 96)
    (Compression.statement w).fee (Range.first_input_range w h)
    (second_input_range w h) (first_output_range w h) (second_output_range w h)
    (public_amount_range w h) (fee_range w h)).mp
  simp only [Compression.statement]
  ring

end MSP.Artifacts.RangeAmounts
