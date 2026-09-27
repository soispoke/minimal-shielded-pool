import Groth16.TwistCardinality
import Groth16.Encoding

/-! Textbook verification for the exact pinned key, using EIP-197's normative
sum-of-discrete-log-products definition of the pairing check. The logarithms
are inverse group isomorphisms, not an efficient algorithm or assumed oracle.
This does not execute the verifier bytecode or prove C9's gas bound. -/
namespace MSP.Groth16

noncomputable def g1Log : G1Point ≃+ F := g1ScalarEquiv.symm
noncomputable def g2Log : G2Point ≃+ F := g2ScalarEquiv.symm

@[simp] theorem g1Log_generator : g1Log g1BasePoint = 1 := by
  rw [← g1ScalarEquiv_one]
  exact g1ScalarEquiv.symm_apply_apply 1
@[simp] theorem g2Log_generator : g2Log g2BasePoint = 1 := by
  rw [← g2ScalarEquiv_one]
  exact g2ScalarEquiv.symm_apply_apply 1

/-- The logarithms are precisely the unique representatives in `[0,p)`. -/
theorem g1Log_spec (P : G1Point) : (g1Log P).val • g1BasePoint = P := by
  rw [← g1ScalarEquiv_natCast, ZMod.natCast_zmod_val]
  exact g1ScalarEquiv.apply_symm_apply P
theorem g2Log_spec (P : G2Point) : (g2Log P).val • g2BasePoint = P := by
  rw [← g2ScalarEquiv_natCast, ZMod.natCast_zmod_val]
  exact g2ScalarEquiv.apply_symm_apply P

/-- EIP-197's field-valued pairing exponent, in its specified generators. -/
noncomputable def pairingExponent (a : G1Point) (b : G2Point) : F := g1Log a * g2Log b

theorem pairingExponent_add_left (a a' : G1Point) (b : G2Point) :
    pairingExponent (a + a') b = pairingExponent a b + pairingExponent a' b := by
  simp only [pairingExponent, map_add, add_mul]
theorem pairingExponent_add_right (a : G1Point) (b b' : G2Point) :
    pairingExponent a (b + b') = pairingExponent a b + pairingExponent a b' := by
  simp only [pairingExponent, map_add, mul_add]

theorem pairingExponent_nonzero_left (a : G1Point) :
    pairingExponent a g2BasePoint = 0 ↔ a = 0 := by
  simp [pairingExponent]
theorem pairingExponent_nonzero_right (b : G2Point) :
    pairingExponent g1BasePoint b = 0 ↔ b = 0 := by
  simp [pairingExponent]

/-- EIP-197 accepts exactly when the sum of products of discrete logs is zero. -/
def PairingCheck (pairs : List (G1Point × G2Point)) : Prop :=
  (pairs.map (fun ab => pairingExponent ab.1 ab.2)).sum = 0

theorem pairingCheck_nil : PairingCheck [] := rfl

/-- The concrete key's three G2 points, with already proved membership. -/
def keyBeta : G2Point := ⟨Subgroup.Beta.point, Subgroup.Beta.p_mul_eq_zero⟩
def keyGamma : G2Point := g2BasePoint
def keyDelta : G2Point := ⟨Subgroup.Delta.point, Subgroup.Delta.p_mul_eq_zero⟩
def keyAlpha : G1Point := Subgroup.Alpha.point
def keyIc (i : Fin 4) : G1Point :=
  (pinnedKey.ic i).toPoint (pinnedKey_coordinateChecks.2.1 i).2.2

/-- Public-signal order is beta, gamma, alpha, matching the committed key. -/
def publicPoint (pub : F × F × F) : G1Point :=
  keyIc 0 + pub.1.val • keyIc 1 + pub.2.1.val • keyIc 2 + pub.2.2.val • keyIc 3

/-- Textbook Groth16's four pairing terms in the linked verifier's order. -/
def VerificationEquation (a : G1Point) (b : G2Point) (c : G1Point)
    (pub : F × F × F) : Prop :=
  PairingCheck [(-a, b), (keyAlpha, keyBeta), (publicPoint pub, keyGamma), (c, keyDelta)]

theorem verificationEquation_iff (a : G1Point) (b : G2Point) (c : G1Point)
    (pub : F × F × F) : VerificationEquation a b c pub ↔
    g1Log a * g2Log b = g1Log keyAlpha * g2Log keyBeta +
      g1Log (publicPoint pub) * g2Log keyGamma + g1Log c * g2Log keyDelta := by
  simp only [VerificationEquation, PairingCheck, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, pairingExponent, map_neg, neg_mul]
  constructor <;> intro h <;> linear_combination -h

/-- Exactly 256 bytes, canonical finite curve points, scalar-order membership
for B, and the textbook pairing equation for the exact pinned verification key.
The full G1 theorem supplies the subgroup checks for A and C. -/
def Accepts (bytes : List UInt8) (pub : F × F × F) : Prop :=
  ∃ π : ProofCoordinates, decodeProof bytes = some π ∧
    ∃ hc : π.OnCurve, ∃ hb : p • π.b.toTwistPoint hc.2.1 = 0,
      VerificationEquation (π.a.toPoint hc.1) ⟨π.b.toTwistPoint hc.2.1, hb⟩
        (π.c.toPoint hc.2.2) pub

theorem accepts_length {bytes : List UInt8} {pub : F × F × F}
    (h : Accepts bytes pub) : bytes.length = 256 := by
  obtain ⟨π, hd, _⟩ := h
  exact decodeProof_length bytes π hd

theorem accepts_point_orders {bytes : List UInt8} {pub : F × F × F}
    (h : Accepts bytes pub) : ∃ π : ProofCoordinates, decodeProof bytes = some π ∧
      ∃ hc : π.OnCurve, addOrderOf (π.a.toPoint hc.1) = p ∧
        addOrderOf (π.b.toTwistPoint hc.2.1) = p ∧
        addOrderOf (π.c.toPoint hc.2.2) = p := by
  obtain ⟨π, hd, hc, hb, _⟩ := h
  let : Fact (Nat.Prime p) := ⟨BN254.ScalarField_is_prime⟩
  exact ⟨π, hd, hc, G1Coordinates.toPoint_order _ _,
    addOrderOf_eq_prime hb (G2Coordinates.toTwistPoint_ne_zero _ _),
    G1Coordinates.toPoint_order _ _⟩

end MSP.Groth16
