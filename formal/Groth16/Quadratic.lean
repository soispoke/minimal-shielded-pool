import Groth16.Group
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! A concrete field for the BN254 quadratic extension and its exact connection
with the `(real, imaginary)` coordinate arithmetic in `Groth16.Curve`.
The product type's ordinary componentwise multiplication is not used. -/

namespace MSP.Groth16

open scoped QuadraticAlgebra

theorem q_mod_four : q % 4 = 3 := by decide

theorem fq_neg_one_not_square : ¬ IsSquare (-1 : Fq) := by
  rw [ZMod.exists_sq_eq_neg_one_iff, q_mod_four]
  exact not_not.mpr rfl

instance fq_neg_one_not_square_fact : Fact (¬ IsSquare (-1 : Fq)) :=
  ⟨fq_neg_one_not_square⟩

/-- The extension `Fq[i]` with `i² = -1`. Its field structure follows from
base-field primality and the proved nonsquareness of `-1`. -/
abbrev FqExt := QuadraticAlgebra Fq (-1) 0

example : Field FqExt := inferInstance

def fqI : FqExt := QuadraticAlgebra.omega

theorem fqI_squared : fqI ^ 2 = -1 := by
  ext <;> simp [fqI, pow_two]

/-- A bijection of representations, with multiplication compatibility proved
explicitly below for `fq2mul`. This is not the product ring structure. -/
def fq2ToField : Fq2 ≃ FqExt := (QuadraticAlgebra.equivProd (-1 : Fq) 0).symm

@[simp] theorem fq2ToField_pair (re im : Fq) :
    fq2ToField (re, im) = ⟨re, im⟩ := rfl

@[simp] theorem fq2ToField_mul (a b : Fq2) :
    fq2ToField (fq2mul a b) = fq2ToField a * fq2ToField b := by
  ext <;> simp [fq2ToField, fq2mul, sub_eq_add_neg]

@[simp] theorem fq2ToField_sub (a b : Fq2) :
    fq2ToField (fq2sub a b) = fq2ToField a - fq2ToField b := by
  ext <;> simp [fq2ToField, fq2sub]

@[simp] theorem fq2ToField_one : fq2ToField (1, 0) = 1 := rfl
@[simp] theorem fq2ToField_zero : fq2ToField (0, 0) = 0 := rfl
@[simp] theorem fq2ToField_three : fq2ToField (3, 0) = 3 := rfl

theorem fq2ToField_nine_one : fq2ToField (9, 1) = 9 + fqI := by
  ext <;> simp [fqI, fq2ToField]

theorem nine_add_fqI_ne_zero : (9 : FqExt) + fqI ≠ 0 := by
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  simp [fqI] at hr
  exact (by decide : (9 : Fq) ≠ 0) hr

theorem fq2ToField_twistInverse : fq2ToField twistInverse = (9 + fqI)⁻¹ := by
  have h := congrArg fq2ToField twistInverse_correct
  rw [fq2ToField_mul, fq2ToField_one, fq2ToField_nine_one] at h
  exact eq_inv_of_mul_eq_one_left h

theorem fq2ToField_twistB : fq2ToField twistB = 3 / (9 + fqI) := by
  rw [twistB, fq2ToField_mul, fq2ToField_three, fq2ToField_twistInverse, div_eq_mul_inv]

/-- The frozen multiplied coordinate check is exactly the usual twist equation
in the actual quadratic extension field. -/
theorem G2Coordinates.onCurve_field_iff (b : G2Coordinates) :
    b.OnCurve ↔
      (fq2ToField (b.yRe, b.yIm)) ^ 2 =
        (fq2ToField (b.xRe, b.xIm)) ^ 3 + 3 / (9 + fqI) := by
  rw [G2Coordinates.onCurve_iff, ← fq2ToField.injective.eq_iff]
  simp only [fq2ToField_sub, fq2ToField_mul, fq2ToField_twistB]
  rw [sub_eq_iff_eq_add]
  ring_nf

end MSP.Groth16
