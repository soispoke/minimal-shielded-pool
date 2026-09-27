import Artifacts.InputNonzero

/-! Construct the inverse required by the actual nonzero-input gate from the
canonical range and positive-value conditions. Whole-assignment construction
remains separate. -/

namespace MSP.Artifacts.InputCompleteness

theorem sum_ne_zero (x y : F) (hx : x.val < 2^128) (hy : y.val < 2^128)
    (hpos : 0 < x.val + y.val) : x + y ≠ 0 := by
  have hbound : 2 * 2^128 < p := by norm_num [p]
  have hsum : x.val + y.val < p := by omega
  intro hz
  have he : x.val + y.val = 0 := MSP.nat_eq_of_field_eq hsum (by norm_num [p])
    (by simpa only [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_zero] using hz)
  omega

/-- Exact constraint 635 holds when its retained inverse wire is assigned
the inverse of the input sum. Positivity and bounds establish invertibility. -/
theorem input_gate_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 10).val < 2^128) (hy : (a 11).val < 2^128)
    (hpos : 0 < (a 10).val + (a 11).val)
    (hinv : a 729 = (a 10 + a 11)⁻¹) : InputNonzero.constraint.Holds a := by
  have hne := sum_ne_zero (a 10) (a 11) hx hy hpos
  simp [InputNonzero.constraint, Constraint.Holds, LinearCombination.eval,
    hzero, hinv, hne]

#print axioms input_gate_complete

end MSP.Artifacts.InputCompleteness
