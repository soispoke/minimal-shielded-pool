import Groth16.SubgroupKey
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.NatCard

/-! Exact G1 cardinality without a Hasse-bound assumption. An injective
coordinate encoding bounds the size by `2*q+1`. A cubic nonresidue certificate
excludes nonzero 2-torsion. The already checked base-point order `p`, Lagrange,
and Cauchy then force the size to be `p`, so the base point generates G1. -/

namespace MSP.Groth16

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-- Choose one of the two possible signs of an affine ordinate. -/
private def ordinateSign (y : Fq) : Bool := decide (y.val ≤ (-y).val)

private theorem ordinateSign_neg_injective (y : Fq)
    (h : ordinateSign y = ordinateSign (-y)) : y = -y := by
  apply ZMod.val_injective q
  unfold ordinateSign at h
  simp only [neg_neg] at h
  by_cases hle : y.val ≤ (-y).val
  · have hge : (-y).val ≤ y.val := by simpa only [hle, decide_true, true_eq_decide_iff] using h
    exact Nat.le_antisymm hle hge
  · have hnge : ¬ (-y).val ≤ y.val := by
      simpa only [hle, decide_false, false_eq_decide_iff] using h
    omega

/-- Infinity, or an abscissa plus one sign bit. This does not enumerate the field. -/
private def g1PointCode : G1Point → Option (Fq × Bool)
  | .zero => none
  | .some x y _ => some (x, ordinateSign y)

private theorem g1PointCode_injective : Function.Injective g1PointCode := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some xx yy hq => cases h
  | some x y hp =>
    cases Q with
    | zero => cases h
    | some xx yy hq =>
      have hc : x = xx ∧ ordinateSign y = ordinateSign yy := by
        simpa only [g1PointCode, Option.some.injEq, Prod.mk.injEq] using h
      rcases hc with ⟨rfl, hs⟩
      have hsq : y ^ 2 = yy ^ 2 :=
        ((g1Curve_nonsingular x y).mp hp).trans ((g1Curve_nonsingular x yy).mp hq).symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hy | hy
      · cases hy
        rfl
      · have hy' : y = yy := by
          rw [hy] at hs ⊢
          exact (ordinateSign_neg_injective yy hs.symm).symm
        cases hy'
        rfl

instance g1Point_finite : Finite G1Point :=
  Finite.of_injective g1PointCode g1PointCode_injective

noncomputable instance g1Point_fintype : Fintype G1Point := Fintype.ofFinite G1Point

theorem g1Point_card_le : Fintype.card G1Point ≤ 2 * q + 1 := by
  rw [← Nat.card_eq_fintype_card]
  have h := Nat.card_le_card_of_injective g1PointCode g1PointCode_injective
  have hc : Nat.card (Option (Fq × Bool)) = 2 * q + 1 := by
    rw [Finite.card_option, Nat.card_prod, Nat.card_zmod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm q 2]
  exact h.trans_eq hc

/-- A checked finite-field obstruction to `x³=-3`. -/
theorem minus_three_cubic_nonresidue : (-3 : Fq) ^ ((q - 1) / 3) ≠ 1 := by
  decide

theorem no_cube_minus_three (x : Fq) : x ^ 3 ≠ -3 := by
  intro hc
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide : 3 ≠ 0)] at hc
    exact (by decide : (0 : Fq) ≠ -3) hc
  have hpow := congrArg (fun a : Fq => a ^ ((q - 1) / 3)) hc
  rw [← pow_mul, show 3 * ((q - 1) / 3) = q - 1 by decide,
    ZMod.pow_card_sub_one_eq_one hx] at hpow
  exact minus_three_cubic_nonresidue hpow.symm

/-- The only rational G1 point killed by two is infinity. -/
theorem g1Point_two_nsmul_eq_zero (P : G1Point) (h : (2 : ℕ) • P = 0) : P = 0 := by
  have hn : P = -P := eq_neg_of_add_eq_zero_left (by simpa only [two_nsmul] using h)
  cases P with
  | zero => rfl
  | some x y hp =>
    have hy : y = -y := by
      have hy' := congrArg (fun P : G1Point => match P with
        | .zero => (0 : Fq)
        | .some _ yy _ => yy) hn
      change y = g1Curve.negY x y at hy'
      simpa [g1Curve] using hy'
    have hz : y = 0 := by
      have hm : (2 : Fq) * y = 0 := by linear_combination hy
      exact (mul_eq_zero.mp hm).resolve_left (by decide)
    have he := (g1Curve_nonsingular x y).mp hp
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at he
    exact False.elim (no_cube_minus_three x (by linear_combination -he))

theorem g1Point_card_not_even : ¬ 2 ∣ Fintype.card G1Point := by
  intro heven
  obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card (G := G1Point) 2 heven
  have hkill : (2 : ℕ) • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  have hzero := g1Point_two_nsmul_eq_zero P hkill
  rw [hzero, addOrderOf_zero] at hP
  omega

/-- Exact cardinality of the full on-curve G1 group. -/
theorem g1Point_card : Fintype.card G1Point = p := by
  have hdvd : p ∣ Fintype.card G1Point := by
    rw [← Subgroup.g1BasePoint_order]
    exact addOrderOf_dvd_card
  obtain ⟨k, hk⟩ := hdvd
  have hpositive := Fintype.card_pos (α := G1Point)
  have hupper := g1Point_card_le
  have hbound : 2 * q + 1 < 3 * p := by decide
  have hp : 0 < p := by decide
  have hklt : k < 3 := by nlinarith
  have hkpos : 0 < k := by nlinarith
  have hkne : k ≠ 2 := by
    intro heq
    apply g1Point_card_not_even
    rw [hk, heq]
    exact dvd_mul_left 2 p
  have hkone : k = 1 := by omega
  simpa only [hkone, mul_one] using hk

theorem g1Point_natCard : Nat.card G1Point = p := by
  rw [Nat.card_eq_fintype_card, g1Point_card]

local instance scalar_prime_fact : Fact (Nat.Prime p) := ⟨BN254.ScalarField_is_prime⟩

/-- Every on-curve point is in the subgroup generated by `(1,2)`. -/
theorem g1BasePoint_generates : AddSubgroup.zmultiples g1BasePoint = ⊤ :=
  zmultiples_eq_top_of_prime_card g1Point_natCard g1BasePoint_ne_zero

/-- Every G1 point has a representative scalar in `[0,p)`. -/
theorem g1Point_exists_scalar (P : G1Point) :
    ∃ n : ℕ, n < p ∧ n • g1BasePoint = P := by
  have hm : P ∈ AddSubgroup.zmultiples g1BasePoint := by
    rw [g1BasePoint_generates]
    trivial
  rw [mem_zmultiples_iff_mem_range_addOrderOf, Subgroup.g1BasePoint_order] at hm
  simpa only [Finset.mem_image, Finset.mem_range] using hm

/-- On-curve-only G1 validation suffices for scalar-prime torsion. -/
theorem g1Point_scalar_prime_torsion (P : G1Point) : p • P = 0 := by
  rw [← g1Point_card]
  exact card_nsmul_eq_zero


/-- The scalar field is additively isomorphic to the full G1 group, sending
one to the conventional base point. This is mathematical, not a discrete-log
algorithm or an extra cryptographic premise. -/
noncomputable def g1ScalarEquiv : F ≃+ G1Point :=
  zmodAddEquivOfGenerator (fun P => by rw [g1BasePoint_generates]; trivial)
    g1Point_natCard

theorem g1ScalarEquiv_one : g1ScalarEquiv 1 = g1BasePoint :=
  zmodAddEquivOfGenerator_apply_one _ _

theorem g1ScalarEquiv_natCast (n : ℕ) : g1ScalarEquiv (n : F) = n • g1BasePoint := by
  simpa [g1ScalarEquiv] using zmodAddEquivOfGenerator_apply_intCast
    (fun P => by rw [g1BasePoint_generates]; trivial) g1Point_natCard (n : ℤ)

/-- Each point has a unique scalar-field representative. -/
theorem g1Point_exists_unique_scalar (P : G1Point) :
    ∃! s : F, g1ScalarEquiv s = P :=
  g1ScalarEquiv.toEquiv.bijective.existsUnique P

/-- A finite on-curve G1 input has exact prime order, without an additional
subgroup-membership assumption. Coordinate canonicity is checked separately. -/
theorem G1Coordinates.toPoint_order (a : G1Coordinates) (h : a.OnCurve) :
    addOrderOf (a.toPoint h) = p :=
  addOrderOf_eq_prime (g1Point_scalar_prime_torsion _) (a.toPoint_ne_zero h)

end MSP.Groth16
