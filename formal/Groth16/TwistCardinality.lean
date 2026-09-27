import Groth16.Cardinality
import Groth16.Cofactor
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.Pairing

/-! The entire scalar-prime torsion subgroup of the actual BN254 twist.
A checked point of order 10069 and a coordinate bound exclude p² dividing
its ambient cardinality. No twist cardinality or Hasse bound is assumed. -/
namespace MSP.Groth16

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

instance fqExt_finite : Finite FqExt := Finite.of_equiv Fq2 fq2ToField
noncomputable instance fqExt_fintype : Fintype FqExt := Fintype.ofFinite FqExt

theorem fqExt_natCard : Nat.card FqExt = q ^ 2 := by
  rw [← Nat.card_congr fq2ToField, Nat.card_prod, Nat.card_zmod]
  rfl

private def ordinateCode (y : FqExt) : ℕ := Nat.pair y.re.val y.im.val
private theorem ordinateCode_injective : Function.Injective ordinateCode := by
  intro a b h
  have hc := Nat.pair_eq_pair.mp h
  apply QuadraticAlgebra.ext
  · exact ZMod.val_injective q hc.1
  · exact ZMod.val_injective q hc.2
private def ordinateSign (y : FqExt) : Bool := decide (ordinateCode y ≤ ordinateCode (-y))
private theorem ordinateSign_neg_injective (y : FqExt)
    (h : ordinateSign y = ordinateSign (-y)) : y = -y := by
  apply ordinateCode_injective
  unfold ordinateSign at h
  simp only [neg_neg] at h
  by_cases hle : ordinateCode y ≤ ordinateCode (-y)
  · have hge : ordinateCode (-y) ≤ ordinateCode y := by
      simpa only [hle, decide_true, true_eq_decide_iff] using h
    exact Nat.le_antisymm hle hge
  · have hnge : ¬ ordinateCode (-y) ≤ ordinateCode y := by
      simpa only [hle, decide_false, false_eq_decide_iff] using h
    omega

private def twistPointCode : TwistPoint → Option (FqExt × Bool)
  | .zero => none
  | .some x y _ => some (x, ordinateSign y)
private theorem twistPointCode_injective : Function.Injective twistPointCode := by
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
        simpa only [twistPointCode, Option.some.injEq, Prod.mk.injEq] using h
      rcases hc with ⟨rfl, hs⟩
      have hsq : y ^ 2 = yy ^ 2 :=
        ((twistCurve_nonsingular x y).mp hp).trans ((twistCurve_nonsingular x yy).mp hq).symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hy | hy
      · cases hy
        rfl
      · have hy' : y = yy := by
          rw [hy] at hs ⊢
          exact (ordinateSign_neg_injective yy hs.symm).symm
        cases hy'
        rfl

instance twistPoint_finite : Finite TwistPoint :=
  Finite.of_injective twistPointCode twistPointCode_injective
noncomputable instance twistPoint_fintype : Fintype TwistPoint := Fintype.ofFinite TwistPoint

theorem twistPoint_card_le : Nat.card TwistPoint ≤ 2 * q ^ 2 + 1 := by
  have h := Nat.card_le_card_of_injective twistPointCode twistPointCode_injective
  have hc : Nat.card (Option (FqExt × Bool)) = 2 * q ^ 2 + 1 := by
    rw [Finite.card_option, Nat.card_prod, fqExt_natCard]
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm (q ^ 2) 2]
  exact h.trans_eq hc

theorem cofactorPoint_order : addOrderOf Subgroup.Cofactor.point = 10069 := by
  let : Fact (Nat.Prime 10069) := ⟨by pratt⟩
  exact addOrderOf_eq_prime Subgroup.Cofactor.cofactor_mul_eq_zero
    Subgroup.Cofactor.point_ne_zero

theorem twistPoint_card_not_scalar_square : ¬ p ^ 2 ∣ Nat.card TwistPoint := by
  intro hp2
  have hc : 10069 ∣ Nat.card TwistPoint := by
    rw [← cofactorPoint_order]
    exact addOrderOf_dvd_natCard Subgroup.Cofactor.point
  have hcp : Nat.Coprime 10069 (p ^ 2) := by decide
  have hd := hcp.mul_dvd_of_dvd_of_dvd hc hp2
  have hpositive : 0 < Nat.card TwistPoint := Nat.card_pos
  have hlo := Nat.le_of_dvd hpositive hd
  have hup := twistPoint_card_le
  have hbound : 2 * q ^ 2 + 1 < 10069 * p ^ 2 := by decide
  omega

/-- Precisely the subgroup tested by EIP-197's scalar-order check. -/
abbrev G2Point := Subgroup.primeTorsion TwistPoint

local instance twist_scalar_prime_fact : Fact (Nat.Prime p) := ⟨BN254.ScalarField_is_prime⟩

/-- The standard G2 generator is the exact gamma point in the pinned key. -/
def g2BasePoint : G2Point := ⟨Subgroup.Gamma.point, Subgroup.Gamma.p_mul_eq_zero⟩

theorem g2BasePoint_ne_zero : g2BasePoint ≠ 0 := by
  intro h
  have he := congrArg Subtype.val h
  exact G2Coordinates.toTwistPoint_ne_zero pinnedKey.gamma2
    pinnedKey_coordinateChecks.2.2.2.1.2.2 he

theorem g2Point_scalar_prime_torsion (P : G2Point) : p • P = 0 := by
  apply Subtype.ext
  exact P.property

theorem g2BasePoint_order : addOrderOf g2BasePoint = p :=
  addOrderOf_eq_prime (g2Point_scalar_prime_torsion _) g2BasePoint_ne_zero

theorem g2Point_natCard : Nat.card G2Point = p := by
  have hg : IsPGroup p (Multiplicative G2Point) := by
    intro P
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    change (p ^ 1) • P.toAdd = 0
    simpa only [pow_one] using g2Point_scalar_prime_torsion P.toAdd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hg
  have hcard : Nat.card G2Point = p ^ n := by simpa using hn
  have hd : Nat.card G2Point ∣ Nat.card TwistPoint :=
    AddSubgroup.card_addSubgroup_dvd_card _
  have hnp : n < 2 := by
    by_contra h
    apply twistPoint_card_not_scalar_square
    exact (pow_dvd_pow p (by omega : 2 ≤ n)).trans (hcard ▸ hd)
  have hpos : n ≠ 0 := by
    intro he
    have hp : p ∣ Nat.card G2Point := by
      rw [← g2BasePoint_order]
      exact addOrderOf_dvd_natCard g2BasePoint
    rw [hcard, he, pow_zero] at hp
    have := Nat.le_of_dvd (by decide : 0 < 1) hp
    have : 1 < p := by decide
    omega
  have hn1 : n = 1 := by omega
  simpa [hn1] using hcard

/-- The standard EIP-197 generator spans the entire scalar-prime torsion. -/
theorem g2BasePoint_generates : AddSubgroup.zmultiples g2BasePoint = ⊤ :=
  zmultiples_eq_top_of_prime_card g2Point_natCard g2BasePoint_ne_zero

noncomputable def g2ScalarEquiv : F ≃+ G2Point :=
  zmodAddEquivOfGenerator (fun P => by rw [g2BasePoint_generates]; trivial)
    g2Point_natCard

theorem g2ScalarEquiv_one : g2ScalarEquiv 1 = g2BasePoint :=
  zmodAddEquivOfGenerator_apply_one _ _

theorem g2ScalarEquiv_natCast (n : ℕ) : g2ScalarEquiv (n : F) = n • g2BasePoint := by
  simpa [g2ScalarEquiv] using zmodAddEquivOfGenerator_apply_intCast
    (fun P => by rw [g2BasePoint_generates]; trivial) g2Point_natCard (n : ℤ)

theorem g2Point_exists_unique_scalar (P : G2Point) :
    ∃! s : F, g2ScalarEquiv s = P :=
  g2ScalarEquiv.toEquiv.bijective.existsUnique P

/-- The usual scalar-order validation is equivalent to membership in the
concrete subgroup generated by the EIP-197 point. -/
theorem twistPoint_mem_g2_iff (P : TwistPoint) :
    p • P = 0 ↔ ∃ n : ℕ, n < p ∧ n • (g2BasePoint : TwistPoint) = P := by
  constructor
  · intro hp
    let Q : G2Point := ⟨P, hp⟩
    have hm : Q ∈ AddSubgroup.zmultiples g2BasePoint := by
      rw [g2BasePoint_generates]
      trivial
    rw [mem_zmultiples_iff_mem_range_addOrderOf, g2BasePoint_order] at hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    exact ⟨n, Finset.mem_range.mp hn, congrArg Subtype.val he⟩
  · rintro ⟨n, _, rfl⟩
    rw [smul_smul, Nat.mul_comm, ← smul_smul]
    change n • (p • Subgroup.Gamma.point) = 0
    rw [Subgroup.Gamma.p_mul_eq_zero]
    exact nsmul_zero n

end MSP.Groth16
