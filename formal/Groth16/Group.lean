import Groth16.Curve
import Primality.BN254Base
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! The actual BN254 base field and the group of rational points on
`y² = x³ + 3`. This uses Mathlib's proved nonsingular Weierstrass group law.
The coordinate correspondence below does not establish the order of the group,
prime-order subgroup membership, the twist group, or a pairing. -/

namespace MSP.Groth16

theorem q_prime : Nat.Prime q := BN254.BaseField_is_prime

instance q_prime_fact : Fact (Nat.Prime q) := ⟨q_prime⟩

/-- The exact base field used by the frozen coordinate checks. -/
instance fq_field : Field Fq := ZMod.instField q

/-- The short Weierstrass model used by EIP-196 and EIP-197 G1. -/
def g1Curve : WeierstrassCurve.Affine Fq := ⟨0, 0, 0, 0, 3⟩

theorem g1Curve_discriminant : g1Curve.Δ = (-3888 : Fq) := by
  norm_num [g1Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem g1Curve_discriminant_ne_zero : g1Curve.Δ ≠ 0 := by
  rw [g1Curve_discriminant]
  decide

instance g1Curve_isElliptic : g1Curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr g1Curve_discriminant_ne_zero⟩

theorem g1Curve_equation (x y : Fq) :
    g1Curve.Equation x y ↔ y ^ 2 = x ^ 3 + 3 := by
  simp [WeierstrassCurve.Affine.equation_iff, g1Curve]

theorem g1Curve_nonsingular (x y : Fq) :
    g1Curve.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 3 := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, g1Curve_equation]

/-- Includes the point at infinity. Its `AddCommGroup` is Mathlib's group law. -/
abbrev G1Point := g1Curve.Point

example : AddCommGroup G1Point := inferInstance

/-- Lift an on-curve affine coordinate pair to the concrete group. -/
def G1Coordinates.toPoint (a : G1Coordinates) (h : a.OnCurve) : G1Point :=
  .some (a.x : Fq) (a.y : Fq) ((g1Curve_nonsingular _ _).mpr h)

theorem G1Coordinates.toPoint_ne_zero (a : G1Coordinates) (h : a.OnCurve) :
    a.toPoint h ≠ 0 := by
  intro he
  cases he

/-- Recover canonical coordinates of a finite point, and `none` at infinity. -/
def G1Point.coordinates : G1Point → Option G1Coordinates
  | .zero => none
  | .some x y _ => some ⟨x.val, y.val⟩

theorem G1Coordinates.toPoint_coordinates (a : G1Coordinates)
    (hc : a.Canonical) (h : a.OnCurve) :
    (a.toPoint h).coordinates = some a := by
  rcases a with ⟨x, y⟩
  simp only [G1Coordinates.toPoint, G1Point.coordinates, G1Coordinates.Canonical] at *
  rw [ZMod.val_natCast_of_lt hc.1, ZMod.val_natCast_of_lt hc.2]

theorem G1Coordinates.toPoint_injective (a b : G1Coordinates)
    (ha : a.Canonical) (hb : b.Canonical) (hca : a.OnCurve) (hcb : b.OnCurve) :
    a.toPoint hca = b.toPoint hcb ↔ a = b := by
  constructor
  · intro h
    have hc := congrArg G1Point.coordinates h
    simpa only [G1Coordinates.toPoint_coordinates _ ha,
      G1Coordinates.toPoint_coordinates _ hb, Option.some.injEq] using hc
  · rintro rfl
    rfl

theorem G1Point.coordinates_checks (P : G1Point) (a : G1Coordinates)
    (h : P.coordinates = some a) : a.Canonical ∧ a.Nonzero ∧ a.OnCurve := by
  cases P with
  | zero => cases h
  | some x y hp =>
    cases h
    refine ⟨⟨ZMod.val_lt x, ZMod.val_lt y⟩, ?_, ?_⟩
    · by_contra hz
      simp only [G1Coordinates.Nonzero, not_or, not_not] at hz
      have hx : x = 0 := (ZMod.val_eq_zero x).mp hz.1
      have hy : y = 0 := (ZMod.val_eq_zero y).mp hz.2
      have he := (g1Curve_nonsingular x y).mp hp
      rw [hx, hy] at he
      norm_num at he
      exact (by decide : (0 : Fq) ≠ 3) he
    · simpa only [G1Coordinates.OnCurve, ZMod.natCast_zmod_val] using
        (g1Curve_nonsingular x y).mp hp

theorem G1Point.coordinates_toPoint (P : G1Point) (a : G1Coordinates)
    (h : P.coordinates = some a) :
    a.toPoint (P.coordinates_checks a h).2.2 = P := by
  cases P with
  | zero => cases h
  | some x y hp =>
    cases h
    simp only [G1Coordinates.toPoint, ZMod.natCast_zmod_val]

/-- The conventional G1 base point. No order or generator theorem is claimed here. -/
def g1BasePoint : G1Point := G1Coordinates.toPoint ⟨1, 2⟩ (by unfold G1Coordinates.OnCurve; decide)

theorem g1BasePoint_coordinates : g1BasePoint.coordinates = some ⟨1, 2⟩ := by
  apply G1Coordinates.toPoint_coordinates
  unfold G1Coordinates.Canonical
  decide

theorem g1BasePoint_ne_zero : g1BasePoint ≠ 0 :=
  G1Coordinates.toPoint_ne_zero _ _

end MSP.Groth16
