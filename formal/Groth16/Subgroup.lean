import Groth16.Twist
import Groth16.KeyData

/-! Generic checked certificates for binary scalar multiplication in the actual
Mathlib elliptic-curve groups. Concrete numerical traces may instantiate these
lemmas; computing a trace outside Lean is not itself a group-membership proof. -/

namespace MSP.Groth16.Subgroup

section Binary
variable {G : Type*} [AddCommGroup G]

/-- One most-significant-bit-first double-and-add step. -/
def binaryStep (P Q : G) (bit : Bool) : G := Q + Q + if bit then P else 0

def binaryValueStep (n : ℕ) (bit : Bool) : ℕ := 2 * n + bit.toNat

theorem binaryStep_nsmul (P : G) (n : ℕ) (bit : Bool) :
    binaryStep P (n • P) bit = binaryValueStep n bit • P := by
  cases bit <;> simp [binaryStep, binaryValueStep, add_nsmul, mul_nsmul, two_nsmul]

/-- Binary double-and-add, with the scalar supplied as a list of bits. -/
def binaryMul (P : G) (bits : List Bool) : G := bits.foldl (binaryStep P) 0

def binaryValue (bits : List Bool) : ℕ := bits.foldl binaryValueStep 0

theorem binaryMul_acc (P : G) (bits : List Bool) (n : ℕ) :
    bits.foldl (binaryStep P) (n • P) = bits.foldl binaryValueStep n • P := by
  induction bits generalizing n with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, binaryStep_nsmul]
    exact ih _

theorem binaryMul_eq_nsmul (P : G) (bits : List Bool) :
    binaryMul P bits = binaryValue bits • P := by
  simpa only [binaryMul, binaryValue, zero_nsmul] using binaryMul_acc P bits 0

/-- Compose a checked numerical step with its established scalar prefix. -/
theorem binaryStep_certificate (P Q R : G) (n : ℕ) (bit : Bool)
    (hq : n • P = Q) (hstep : binaryStep P Q bit = R) :
    binaryValueStep n bit • P = R := by
  rw [← binaryStep_nsmul, hq, hstep]

end Binary

section Affine
variable {K : Type*} [Field K] [DecidableEq K]

def shortCurve (c : K) : WeierstrassCurve.Affine K := ⟨0, 0, 0, 0, c⟩

/-- A tangent slope and its output coordinates certify the actual group double.
No inverse computation or guessed addition law is trusted. -/
theorem double_certificate {c x y xr yr : K}
    {hp : (shortCurve c).Nonsingular x y}
    {hr : (shortCurve c).Nonsingular xr yr} (m : K)
    (hn : y ≠ -y) (hm : m * (y - -y) = 3 * x ^ 2)
    (hx : m ^ 2 - x - x = xr) (hy : m * (x - xr) - y = yr) :
    (WeierstrassCurve.Affine.Point.some x y hp) + .some x y hp = .some xr yr hr := by
  have hn' : y ≠ (shortCurve c).negY x y := by simpa [shortCurve] using hn
  have hs : (shortCurve c).slope x x y y = m := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn']
    simp only [shortCurve, WeierstrassCurve.Affine.negY, zero_mul, mul_zero,
      add_zero, sub_zero]
    exact (div_eq_iff (sub_ne_zero.mpr hn)).mpr hm.symm
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn']
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  rw [hs]
  constructor
  · simpa only [WeierstrassCurve.Affine.addX, shortCurve, zero_mul,
      add_zero, sub_zero] using hx
  · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, shortCurve,
      zero_mul, add_zero, sub_zero]
    rw [hx]
    linear_combination hy

/-- A secant slope and output coordinates certify the actual group addition. -/
theorem add_certificate {c x y xx yy xr yr : K}
    {hp : (shortCurve c).Nonsingular x y}
    {hq : (shortCurve c).Nonsingular xx yy}
    {hr : (shortCurve c).Nonsingular xr yr} (m : K)
    (hn : x ≠ xx) (hm : m * (x - xx) = y - yy)
    (hx : m ^ 2 - x - xx = xr) (hy : m * (x - xr) - y = yr) :
    (WeierstrassCurve.Affine.Point.some x y hp) + .some xx yy hq = .some xr yr hr := by
  have hs : (shortCurve c).slope x xx y yy = m := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hn]
    exact (div_eq_iff (sub_ne_zero.mpr hn)).mpr hm.symm
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hn]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  rw [hs]
  constructor
  · simpa only [WeierstrassCurve.Affine.addX, shortCurve, zero_mul,
      add_zero, sub_zero] using hx
  · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, shortCurve,
      zero_mul, add_zero, sub_zero]
    rw [hx]
    linear_combination hy

/-- Opposite affine points add to the group identity. -/
theorem opposite_certificate {c x y xx yy : K}
    {hp : (shortCurve c).Nonsingular x y}
    {hq : (shortCurve c).Nonsingular xx yy}
    (hx : x = xx) (hy : y = -yy) :
    (WeierstrassCurve.Affine.Point.some x y hp) + .some xx yy hq = 0 := by
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq hx
  simpa [shortCurve] using hy

end Affine
end MSP.Groth16.Subgroup
