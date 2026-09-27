import Groth16.SubgroupAlpha
import Groth16.SubgroupBase
import Groth16.SubgroupIc0
import Groth16.SubgroupIc1
import Groth16.SubgroupIc2
import Groth16.SubgroupIc3
import Groth16.SubgroupBeta
import Groth16.SubgroupGamma
import Groth16.SubgroupDelta
import Primality.BN254
import Mathlib.GroupTheory.OrderOfElement

/-! Exact scalar-prime torsion and point-order certificates for every point in
the pinned Groth16 verification key. These do not assert that all twist points
belong to this torsion subgroup or establish any pairing relation. -/

namespace MSP.Groth16.Subgroup

/-- Points killed by the scalar prime form a subgroup of either ambient group. -/
def primeTorsion (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := {P | p • P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change p • a = 0 at ha
    change p • b = 0 at hb
    change p • (a + b) = 0
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    change p • a = 0 at ha
    change p • (-a) = 0
    rw [smul_neg, ha, neg_zero]

@[simp] theorem mem_primeTorsion {G : Type*} [AddCommGroup G] (P : G) :
    P ∈ primeTorsion G ↔ p • P = 0 := Iff.rfl

local instance scalar_prime_fact : Fact (Nat.Prime p) := ⟨BN254.ScalarField_is_prime⟩

/-- Exact key-coordinate projections into the actual groups are killed by `p`. -/
theorem pinnedKey_subgroupChecks :
    p • pinnedKey.alpha1.toPoint pinnedKey_coordinateChecks.1.2.2 = 0 ∧
    (∀ i : Fin 4, p • (pinnedKey.ic i).toPoint
      (pinnedKey_coordinateChecks.2.1 i).2.2 = 0) ∧
    p • pinnedKey.beta2.toTwistPoint pinnedKey_coordinateChecks.2.2.1.2.2 = 0 ∧
    p • pinnedKey.gamma2.toTwistPoint pinnedKey_coordinateChecks.2.2.2.1.2.2 = 0 ∧
    p • pinnedKey.delta2.toTwistPoint pinnedKey_coordinateChecks.2.2.2.2.2.2 = 0 := by
  refine ⟨Alpha.p_mul_eq_zero, ?_, Beta.p_mul_eq_zero, Gamma.p_mul_eq_zero, Delta.p_mul_eq_zero⟩
  intro i
  fin_cases i
  · exact Ic0.p_mul_eq_zero
  · exact Ic1.p_mul_eq_zero
  · exact Ic2.p_mul_eq_zero
  · exact Ic3.p_mul_eq_zero

/-- Every pinned finite G1 and twist point has exact order `p`. This follows
from the checked multiples, primality of `p`, and non-infinity. -/
theorem pinnedKey_pointOrders :
    addOrderOf (pinnedKey.alpha1.toPoint pinnedKey_coordinateChecks.1.2.2) = p ∧
    (∀ i : Fin 4, addOrderOf ((pinnedKey.ic i).toPoint
      (pinnedKey_coordinateChecks.2.1 i).2.2) = p) ∧
    addOrderOf (pinnedKey.beta2.toTwistPoint pinnedKey_coordinateChecks.2.2.1.2.2) = p ∧
    addOrderOf (pinnedKey.gamma2.toTwistPoint pinnedKey_coordinateChecks.2.2.2.1.2.2) = p ∧
    addOrderOf (pinnedKey.delta2.toTwistPoint pinnedKey_coordinateChecks.2.2.2.2.2.2) = p := by
  refine ⟨addOrderOf_eq_prime pinnedKey_subgroupChecks.1 (G1Coordinates.toPoint_ne_zero _ _),
    ?_, addOrderOf_eq_prime pinnedKey_subgroupChecks.2.2.1 (G2Coordinates.toTwistPoint_ne_zero _ _),
    addOrderOf_eq_prime pinnedKey_subgroupChecks.2.2.2.1 (G2Coordinates.toTwistPoint_ne_zero _ _),
    addOrderOf_eq_prime pinnedKey_subgroupChecks.2.2.2.2 (G2Coordinates.toTwistPoint_ne_zero _ _)⟩
  intro i
  exact addOrderOf_eq_prime (pinnedKey_subgroupChecks.2.1 i) (G1Coordinates.toPoint_ne_zero _ _)

theorem g1BasePoint_order : addOrderOf g1BasePoint = p :=
  addOrderOf_eq_prime Base.p_mul_eq_zero g1BasePoint_ne_zero

end MSP.Groth16.Subgroup
