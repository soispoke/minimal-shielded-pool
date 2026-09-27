import Artifacts.RangeGate
import Proofs.CircuitCompleteness

/-! Constructive counterpart of the optimized range-gate algebra. Canonical
low bits force the eliminated high bit to its canonical value. The shape and
reconstruction equations are to be discharged for each pinned gate; this does
not yet construct an assignment of the complete spend circuit. -/

namespace MSP.Artifacts.RangeCompleteness

open RangeLemmas RangeGate MSP.CircuitCompleteness

theorem canonical_reconstruction (a : Assignment) (start n : ℕ) (x : F)
    (hx : x.val < 2^(n+1))
    (hbits : ∀ i < n, a (start + i) = bitDigit x.val i) :
    (weightedWires start n).eval a + (2 : F)^n * bitDigit x.val n = x := by
  have hcanon : canonicalBits (n+1) x.val =
      ((List.range n).map fun i => a (start+i)) ++ [bitDigit x.val n] := by
    unfold canonicalBits
    rw [List.range_succ, List.map_append]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact (hbits i (List.mem_range.mp hi)).symm
  have h := canonicalBits_field x (n+1) hx
  rw [hcanon, bitsField_wires_append] at h
  exact h

theorem eliminated_bit (a : Assignment) (start n : ℕ) (x top : F)
    (hx : x.val < 2^(n+1))
    (hbits : ∀ i < n, a (start + i) = bitDigit x.val i)
    (hrec : (weightedWires start n).eval a + (2 : F)^n * top = x) :
    top = bitDigit x.val n := by
  have h2 : (2 : F) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    change 2 % p = 0 at hv
    norm_num [p] at hv
  apply mul_left_cancel₀ (pow_ne_zero n h2)
  exact add_left_cancel (hrec.trans (canonical_reconstruction a start n x hx hbits).symm)

/-- Satisfy all retained Boolean constraints and the eliminated top-bit
constraint from the canonical bit assignment and the actual reconstruction. -/
theorem gate_complete (a : Assignment) (hzero : a 0 = 1) (start n : ℕ)
    (top : Constraint) (x : F) (hx : x.val < 2^(n+1))
    (hbits : ∀ i < n, a (start + i) = bitDigit x.val i)
    (ha : top.a = (0, p-1) :: top.b) (hc : top.c = [])
    (hrec : (weightedWires start n).eval a + (2 : F)^n * top.b.eval a = x) :
    (∀ i < n, (lowConstraint start i).Holds a) ∧ top.Holds a := by
  have ht := eliminated_bit a start n x (top.b.eval a) hx hbits hrec
  constructor
  · intro i hi
    have hb := bitDigit_boolean x.val i
    simp only [lowConstraint, Constraint.Holds, LinearCombination.eval,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one,
      one_mul, add_zero, coefficient_neg_one, hzero, mul_one, hbits i hi]
    linear_combination hb
  · have hA : top.a.eval a = -1 + top.b.eval a := by
      simp only [ha, LinearCombination.eval, List.map_cons, List.sum_cons,
        coefficient_neg_one, hzero, mul_one]
    have hC : top.c.eval a = 0 := by simp [hc, LinearCombination.eval]
    unfold Constraint.Holds
    rw [hA, hC, ht]
    linear_combination bitDigit_boolean x.val n

#print axioms gate_complete

end MSP.Artifacts.RangeCompleteness
