import Spec.Basic
import Mathlib.Tactic

/-!
Arithmetic helpers for `Spend` in `circuits/spend.circom`: its six 128-bit
values cannot wrap either side of the conservation equation in BN254's scalar
field. These lemmas do not bind the circuit or its compiled constraints.
-/

namespace MSP

/-- Equality of natural numbers below the scalar modulus is preserved by
casting into the scalar field. -/
theorem nat_eq_of_field_eq {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : F) = (b : F)) : a = b := by
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

/-- The circuit's field conservation equation is exactly integer conservation
when all six amounts have the required 128-bit range. -/
theorem value_conservation_iff (a b c d pub fee : F)
    (ha : a.val < 2 ^ 128) (hb : b.val < 2 ^ 128)
    (hc : c.val < 2 ^ 128) (hd : d.val < 2 ^ 128)
    (hpub : pub.val < 2 ^ 128) (hfee : fee.val < 2 ^ 128) :
    a + b = c + d + pub + fee ↔
      a.val + b.val = c.val + d.val + pub.val + fee.val := by
  have hbound : 4 * 2 ^ 128 < p := by norm_num [p]
  have hin : a.val + b.val < p := by omega
  have hout : c.val + d.val + pub.val + fee.val < p := by omega
  constructor
  · intro heq
    apply nat_eq_of_field_eq hin hout
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using heq
  · intro heq
    have hcast := congrArg (fun n : ℕ => (n : F)) heq
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hcast

/-- A nonzero input sum in the field consumes positive integer value. -/
theorem input_sum_pos (a b : F) (h : a + b ≠ 0) : 0 < a.val + b.val := by
  by_contra hn
  have ha : a.val = 0 := by omega
  have hb : b.val = 0 := by omega
  have haz : a = 0 := (ZMod.val_eq_zero a).1 ha
  have hbz : b = 0 := (ZMod.val_eq_zero b).1 hb
  exact h (by simp [haz, hbz])

#print axioms nat_eq_of_field_eq
#print axioms value_conservation_iff
#print axioms input_sum_pos

end MSP
