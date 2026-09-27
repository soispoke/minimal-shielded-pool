import Groth16.Quadratic

/-! The nonsingular BN254 twist over the proved quadratic extension field.
`TwistPoint` is the full group of rational points. It is not asserted to be the
prime-order G2 subgroup, and no pairing or subgroup-membership result is assumed. -/

namespace MSP.Groth16

open scoped QuadraticAlgebra

def twistCoeff : FqExt := fq2ToField twistB

theorem twistCoeff_eq : twistCoeff = 3 / (9 + fqI) := fq2ToField_twistB

theorem twistCoeff_ne_zero : twistCoeff ≠ 0 := by
  rw [twistCoeff_eq]
  apply div_ne_zero _ nine_add_fqI_ne_zero
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  exact (by decide : (3 : Fq) ≠ 0) hr

def twistCurve : WeierstrassCurve.Affine FqExt := ⟨0, 0, 0, 0, twistCoeff⟩

theorem twistCurve_discriminant : twistCurve.Δ = -432 * twistCoeff ^ 2 := by
  simp only [twistCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem twistCurve_discriminant_ne_zero : twistCurve.Δ ≠ 0 := by
  rw [twistCurve_discriminant]
  apply mul_ne_zero _ (pow_ne_zero _ twistCoeff_ne_zero)
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  exact (by decide : (-432 : Fq) ≠ 0) hr

instance twistCurve_isElliptic : twistCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr twistCurve_discriminant_ne_zero⟩

theorem twistCurve_equation (x y : FqExt) :
    twistCurve.Equation x y ↔ y ^ 2 = x ^ 3 + 3 / (9 + fqI) := by
  simp [WeierstrassCurve.Affine.equation_iff, twistCurve, twistCoeff_eq]

theorem twistCurve_nonsingular (x y : FqExt) :
    twistCurve.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 3 / (9 + fqI) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, twistCurve_equation]

/-- The full twist point group, including infinity, with Mathlib's group law. -/
abbrev TwistPoint := twistCurve.Point

example : AddCommGroup TwistPoint := inferInstance

def G2Coordinates.toTwistPoint (b : G2Coordinates) (h : b.OnCurve) : TwistPoint :=
  .some (fq2ToField (b.xRe, b.xIm)) (fq2ToField (b.yRe, b.yIm))
    ((twistCurve_nonsingular _ _).mpr (b.onCurve_field_iff.mp h))

theorem G2Coordinates.toTwistPoint_ne_zero (b : G2Coordinates) (h : b.OnCurve) :
    b.toTwistPoint h ≠ 0 := by
  intro he
  cases he

def TwistPoint.coordinates : TwistPoint → Option G2Coordinates
  | .zero => none
  | .some x y _ => some ⟨x.re.val, x.im.val, y.re.val, y.im.val⟩

theorem G2Coordinates.toTwistPoint_coordinates (b : G2Coordinates)
    (hc : b.Canonical) (h : b.OnCurve) :
    (b.toTwistPoint h).coordinates = some b := by
  rcases b with ⟨xr, xi, yr, yi⟩
  simp only [G2Coordinates.Canonical] at hc
  simp only [G2Coordinates.toTwistPoint, TwistPoint.coordinates, fq2ToField_pair]
  rw [ZMod.val_natCast_of_lt hc.1, ZMod.val_natCast_of_lt hc.2.1,
    ZMod.val_natCast_of_lt hc.2.2.1, ZMod.val_natCast_of_lt hc.2.2.2]

theorem G2Coordinates.toTwistPoint_injective (a b : G2Coordinates)
    (ha : a.Canonical) (hb : b.Canonical) (hca : a.OnCurve) (hcb : b.OnCurve) :
    a.toTwistPoint hca = b.toTwistPoint hcb ↔ a = b := by
  constructor
  · intro h
    have hc := congrArg TwistPoint.coordinates h
    simpa only [G2Coordinates.toTwistPoint_coordinates _ ha,
      G2Coordinates.toTwistPoint_coordinates _ hb, Option.some.injEq] using hc
  · rintro rfl
    rfl

theorem G2Coordinates.onCurve_nonzero (b : G2Coordinates) (h : b.OnCurve) :
    b.Nonzero := by
  by_contra hn
  simp only [G2Coordinates.Nonzero, not_or, not_not] at hn
  have he := b.onCurve_field_iff.mp h
  rcases hn with ⟨hxr, hxi, hyr, hyi⟩
  rw [hxr, hxi, hyr, hyi] at he
  simp only [Nat.cast_zero, fq2ToField_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_add] at he
  exact twistCoeff_ne_zero (twistCoeff_eq.trans he.symm)

theorem TwistPoint.coordinates_checks (P : TwistPoint) (b : G2Coordinates)
    (h : P.coordinates = some b) : b.Canonical ∧ b.Nonzero ∧ b.OnCurve := by
  cases P with
  | zero => cases h
  | some x y hp =>
    cases h
    have he : (G2Coordinates.mk x.re.val x.im.val y.re.val y.im.val).OnCurve := by
      rw [G2Coordinates.onCurve_field_iff]
      simpa only [fq2ToField_pair, ZMod.natCast_zmod_val, QuadraticAlgebra.mk_eta] using
        (twistCurve_nonsingular x y).mp hp
    exact ⟨⟨ZMod.val_lt x.re, ZMod.val_lt x.im, ZMod.val_lt y.re, ZMod.val_lt y.im⟩,
      G2Coordinates.onCurve_nonzero _ he, he⟩

theorem TwistPoint.coordinates_toTwistPoint (P : TwistPoint) (b : G2Coordinates)
    (h : P.coordinates = some b) :
    b.toTwistPoint (P.coordinates_checks b h).2.2 = P := by
  cases P with
  | zero => cases h
  | some x y hp =>
    cases h
    simp only [G2Coordinates.toTwistPoint, fq2ToField_pair,
      ZMod.natCast_zmod_val, QuadraticAlgebra.mk_eta]

end MSP.Groth16
