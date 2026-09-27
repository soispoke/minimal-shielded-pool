import Artifacts.RangeLemmas

/-!
# Optimized 160-bit address-gate algebra

These lemmas interpret actual constraint coefficient lists. Callers must prove
membership in the full R1CS, gate shapes, and coefficient certificates.
-/

namespace MSP.Artifacts.RangeAddressGate

open RangeLemmas

/-- The retained-bit constraint emitted in this pinned R1CS. -/
def lowConstraint (start i : ℕ) : Constraint :=
  ⟨[(0, p - 1), (start + i, 1)], [(start + i, 1)], []⟩

theorem coefficient_neg_one : ((p - 1 : ℕ) : F) = -1 := by
  norm_num [p]
  apply eq_neg_of_add_eq_zero_left
  norm_num
  exact ZMod.natCast_self p

private def evalFieldPairs (lc : List (ℕ × F)) (w : Assignment) : F :=
  (lc.map fun t => t.2 * w t.1).sum

private theorem evalFieldPairs_scale (lc : LinearCombination) (k : F) (w : Assignment) :
    evalFieldPairs (lc.map fun t => (t.1, k * (t.2 : F))) w = k * lc.eval w := by
  simp only [evalFieldPairs, LinearCombination.eval, List.map_map, Function.comp_def,
    mul_assoc, List.sum_map_mul_left]

private theorem evalFieldPairs_cast (lc : LinearCombination) (w : Assignment) :
    evalFieldPairs (lc.map fun t => (t.1, (t.2 : F))) w = lc.eval w := by
  simp only [evalFieldPairs, LinearCombination.eval, List.map_map, Function.comp_def]

private theorem evalFieldPairs_neg (lc : LinearCombination) (w : Assignment) :
    evalFieldPairs (lc.map fun t => (t.1, -(t.2 : F))) w = -(lc.eval w) := by
  simpa only [neg_one_mul] using evalFieldPairs_scale lc (-1) w

private theorem evalFieldPairs_append (a b : List (ℕ × F)) (w : Assignment) :
    evalFieldPairs (a ++ b) w = evalFieldPairs a w + evalFieldPairs b w := by
  simp only [evalFieldPairs, List.map_append, List.sum_append]

/-- A coefficient permutation is checked in the field and retains every term.
It accounts for every term in the actual eliminated address-bit gate. -/
theorem reconstruction_of_coefficients (topB amount : LinearCombination) (start : ℕ)
    (certificate :
      (topB.map fun t => (t.1, (2 : F)^159 * (t.2 : F))).Perm
        ((amount.map fun t => (t.1, (t.2 : F))) ++
          ((weightedWires start 159).map fun t => (t.1, -(t.2 : F)))))
    (w : Assignment) :
    (weightedWires start 159).eval w + (2 : F)^159 * topB.eval w = amount.eval w := by
  have h : evalFieldPairs (topB.map fun t => (t.1, (2 : F)^159 * (t.2 : F))) w =
      evalFieldPairs ((amount.map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires start 159).map fun t => (t.1, -(t.2 : F)))) w :=
    (certificate.map (fun t : ℕ × F => t.2 * w t.1)).sum_eq
  rw [evalFieldPairs_scale, evalFieldPairs_append, evalFieldPairs_cast,
    evalFieldPairs_neg] at h
  exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp (by simpa only [sub_eq_add_neg] using h))

/-- Soundness of the actual retained/top-bit gate shape. All shape and
reconstruction facts are explicit premises discharged by the artifact caller. -/
theorem gate160_range (w : Assignment) (hzero : w 0 = 1) (start : ℕ)
    (top : Constraint) (x : F)
    (hlow : ∀ i < 159, (lowConstraint start i).Holds w)
    (htop : top.Holds w)
    (ha : top.a = (0, p - 1) :: top.b) (hc : top.c = [])
    (hreconstruct : (weightedWires start 159).eval w + (2 : F)^159 * top.b.eval w = x) :
    x.val < 2^160 := by
  apply num2Bits_wires_range w start 159 (top.b.eval w) x
  · intro i hi
    have h := hlow i hi
    simp only [lowConstraint, Constraint.Holds, LinearCombination.eval, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] at h
    rw [coefficient_neg_one, hzero] at h
    linear_combination h
  · have hA : top.a.eval w = ((p - 1 : ℕ) : F) * w 0 + top.b.eval w := by
      rw [ha]
      simp only [LinearCombination.eval, List.map_cons, List.sum_cons]
    have hC : top.c.eval w = 0 := by simp only [hc, LinearCombination.eval, List.map_nil, List.sum_nil]
    unfold Constraint.Holds at htop
    rw [hA, hC, coefficient_neg_one, hzero] at htop
    linear_combination htop
  · norm_num [p]
  · exact hreconstruct

end MSP.Artifacts.RangeAddressGate
