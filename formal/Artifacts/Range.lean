import Artifacts.RangeData
import Artifacts.RangeLemmas
import Artifacts.Spend

/-!
# First input's actual range gate

This module binds the first 128-bit amount gate to the complete pinned R1CS.
The optimized top bit is the linear combination in the actual last constraint;
its reconstruction identity is checked from those exact field coefficients.
The other five amount gates and integer conservation are proved in RangeAmounts.
The remaining C1/C1c obligations are separate.
-/

namespace MSP.Artifacts.Range

open RangeData RangeLemmas

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Exact full-system location of the generated gate data. -/
theorem constraints_eq_slice :
    RangeData.constraints = (Spend.group54.drop 46).take 128 := rfl

theorem constraints_mem {c : Constraint} (hc : c ∈ RangeData.constraints) :
    c ∈ Spend.system.constraints := by
  rw [constraints_eq_slice] at hc
  apply List.mem_flatten.mpr
  exact ⟨Spend.group54, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private def lowConstraint (i : ℕ) : Constraint :=
  ⟨[(0, p - 1), (13918 + i, 1)], [(13918 + i, 1)], []⟩

private theorem lowConstraints_eq :
    lowConstraints = (List.range 127).map lowConstraint := rfl

private theorem coefficient_neg_one : ((p - 1 : ℕ) : F) = -1 := by
  norm_num [p]
  apply eq_neg_of_add_eq_zero_left
  norm_num
  exact ZMod.natCast_self p

/-- This is the actual B linear combination, not an assumed witness value. -/
def highBit (w : Assignment) : F := topConstraint.b.eval w

private theorem scaled_coefficients :
    (topConstraint.b.map fun t => (t.1, (2 : F)^127 * (t.2 : F))) =
      (10, (1 : F)) :: ((weightedWires 13918 127).map fun t => (t.1, (-1 : F) * (t.2 : F))) := by
  decide

private def evalFieldPairs (lc : List (ℕ × F)) (w : Assignment) : F :=
  (lc.map fun t => t.2 * w t.1).sum

private theorem evalFieldPairs_scale (lc : LinearCombination) (k : F) (w : Assignment) :
    evalFieldPairs (lc.map fun t => (t.1, k * (t.2 : F))) w = k * lc.eval w := by
  simp only [evalFieldPairs, LinearCombination.eval, List.map_map, Function.comp_def,
    mul_assoc, List.sum_map_mul_left]

private theorem evalFieldPairs_cons (t : ℕ × F) (lc : List (ℕ × F)) (w : Assignment) :
    evalFieldPairs (t :: lc) w = t.2 * w t.1 + evalFieldPairs lc w := by
  simp only [evalFieldPairs, List.map_cons, List.sum_cons]

/-- The exact eliminated-bit coefficients reconstruct wire 10. -/
theorem reconstruction (w : Assignment) :
    (weightedWires 13918 127).eval w + (2 : F)^127 * highBit w = w 10 := by
  have h := congrArg (fun lc => evalFieldPairs lc w) scaled_coefficients
  rw [evalFieldPairs_scale, evalFieldPairs_cons, one_mul, evalFieldPairs_scale] at h
  unfold highBit
  linear_combination h

private theorem low_boolean (w : Assignment) (h : Spend.system.Satisfied w)
    (i : ℕ) (hi : i < 127) : w (13918 + i) * (w (13918 + i) - 1) = 0 := by
  have hm : lowConstraint i ∈ RangeData.constraints := by
    apply List.mem_append_left
    rw [lowConstraints_eq]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hc : (lowConstraint i).Holds w := h.2 _ (constraints_mem hm)
  simp only [lowConstraint, Constraint.Holds, LinearCombination.eval, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] at hc
  rw [coefficient_neg_one, h.1] at hc
  linear_combination hc

private theorem high_boolean (w : Assignment) (h : Spend.system.Satisfied w) :
    highBit w * (highBit w - 1) = 0 := by
  have hm : topConstraint ∈ RangeData.constraints := by simp [RangeData.constraints]
  have hc := h.2 _ (constraints_mem hm)
  change ((((p - 1 : ℕ) : F) * w 0 + highBit w) * highBit w = 0) at hc
  rw [coefficient_neg_one, h.1] at hc
  linear_combination hc

/-- The first input amount lies below 2^128 for every satisfying assignment of
all pinned constraints, without trusting the witness calculator. -/
theorem first_input_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 10).val < 2^128 := by
  exact num2Bits_wires_range w 13918 127 (highBit w) (w 10)
    (low_boolean w h) (high_boolean w h) (by norm_num [p]) (reconstruction w)

end MSP.Artifacts.Range
