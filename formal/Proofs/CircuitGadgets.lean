import Spec.Basic
import Primality.BN254
import Mathlib.Tactic

/-! Algebraic helpers for the pinned circomlib IsZero and Boolean constraints.
These describe the constraints themselves, not trusted witness generation.
The `Artifacts` gate proofs apply them to the pinned R1CS for C1 and C1c. -/

namespace MSP

/-- Kernel-checked primality of the scalar modulus used by the circuit. -/
theorem scalar_prime : Nat.Prime p := BN254.ScalarField_is_prime

instance : Fact p.Prime := ⟨scalar_prime⟩

/-- The Boolean constraint admits exactly zero and one. -/
theorem boolean_constraint (b : F) : b * (b - 1) = 0 ↔ b = 0 ∨ b = 1 := by
  rw [mul_eq_zero, sub_eq_zero]

/-- IsZero's inverse witness is arbitrary; its two equations determine the
correct Boolean output even for a maliciously chosen witness. -/
theorem isZero_sound (x inv out : F)
    (hdef : out = 1 - x * inv) (hgate : x * out = 0) :
    (out = 1 ↔ x = 0) ∧ (out = 0 ↔ x ≠ 0) := by
  by_cases hx : x = 0
  · subst x
    simp only [zero_mul, sub_zero] at hdef
    subst out
    simp
  · have hout : out = 0 := (mul_eq_zero.mp hgate).resolve_left hx
    simp [hout, hx]

/-- Every input admits an inverse witness with the correct IsZero output. -/
theorem isZero_complete (x : F) :
    ∃ inv out : F, out = 1 - x * inv ∧ x * out = 0 ∧
      out = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, 1, by simp, by simp, by simp⟩
  · exact ⟨x⁻¹, 0, by simp [hx], by simp, by simp [hx]⟩

/-- Little-endian natural value of a list of field-valued bits. -/
def bitsValue : List F → ℕ
  | [] => 0
  | b :: bs => b.val + 2 * bitsValue bs

/-- The same reconstruction in the circuit's field. -/
def bitsField : List F → F
  | [] => 0
  | b :: bs => b + 2 * bitsField bs

theorem bitsValue_cast (bs : List F) : (bitsValue bs : F) = bitsField bs := by
  induction bs with
  | nil => simp [bitsValue, bitsField]
  | cons b bs ih => simp [bitsValue, bitsField, Nat.cast_add, Nat.cast_mul, ih]

theorem bitsValue_lt (bs : List F)
    (hbits : ∀ b ∈ bs, b * (b - 1) = 0) : bitsValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    have hb : b.val < 2 := by
      rcases (boolean_constraint b).mp (hbits b (by simp)) with h | h
      · simp [h]
      · subst b
        change 1 % p < 2
        norm_num [p]
    have hi := ih (fun b' hb' => hbits b' (by simp [hb']))
    simp only [bitsValue, List.length_cons, pow_succ]
    omega

/-- Boolean decomposition forces the advertised integer range when the bit
width fits below the modulus; this includes MSP's 20-, 128- and 160-bit gates. -/
theorem num2Bits_range (x : F) (bs : List F)
    (hbits : ∀ b ∈ bs, b * (b - 1) = 0)
    (hsize : 2 ^ bs.length ≤ p) (hreconstruct : bitsField bs = x) :
    x.val < 2 ^ bs.length := by
  have hv := bitsValue_lt bs hbits
  have hp : bitsValue bs < p := lt_of_lt_of_le hv hsize
  rw [← hreconstruct, ← bitsValue_cast bs, ZMod.val_natCast, Nat.mod_eq_of_lt hp]
  exact hv

#print axioms scalar_prime
#print axioms boolean_constraint
#print axioms isZero_sound
#print axioms isZero_complete
#print axioms bitsValue_cast
#print axioms bitsValue_lt
#print axioms num2Bits_range

end MSP
