import Proofs.CircuitGadgets
import Mathlib.Data.Nat.Bits

/-! Canonical witnesses for Boolean decomposition. These low-level helpers
construct bits without depending on the artifact soundness proofs. Assigning
all retained R1CS wires and checking their constraints is a separate step. -/

namespace MSP.CircuitCompleteness

/-- The field-valued digit selected by `Nat.testBit`. -/
def bitDigit (value index : ℕ) : F := ((value.testBit index).toNat : F)

/-- Exactly `width` little-endian digits, including leading zeroes. -/
def canonicalBits (width value : ℕ) : List F :=
  (List.range width).map (bitDigit value)

theorem bitDigit_eq (value index : ℕ) :
    bitDigit value index = if value.testBit index then (1 : F) else 0 := by
  cases h : value.testBit index <;> simp [bitDigit, h]

theorem bitDigit_boolean (value index : ℕ) :
    bitDigit value index * (bitDigit value index - 1) = 0 := by
  rw [bitDigit_eq]
  cases value.testBit index <;> simp

theorem bitDigit_val (value index : ℕ) :
    (bitDigit value index).val = (value.testBit index).toNat := by
  cases h : value.testBit index <;> norm_num [bitDigit, h, ZMod.val_natCast, p]
  change 1 % p = 1
  norm_num [p]

theorem canonicalBits_length (width value : ℕ) :
    (canonicalBits width value).length = width := by
  simp [canonicalBits]

theorem canonicalBits_boolean (width value : ℕ) :
    ∀ b ∈ canonicalBits width value, b * (b - 1) = 0 := by
  intro b hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  exact bitDigit_boolean value i

theorem canonicalBits_get (width value index : ℕ) (hi : index < width) :
    (canonicalBits width value)[index]'(by simpa [canonicalBits] using hi) =
      if value.testBit index then (1 : F) else 0 := by
  simp only [canonicalBits, List.getElem_map, List.getElem_range, bitDigit_eq]

theorem canonicalBits_succ (width value : ℕ) :
    canonicalBits (width + 1) value =
      bitDigit value 0 :: canonicalBits width (value / 2) := by
  simp only [canonicalBits, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [bitDigit, Nat.testBit_succ]

/-- The canonical digits reconstruct the original natural number, without
requiring the bit width itself to fit below the scalar modulus. -/
theorem canonicalBits_value (width value : ℕ) (h : value < 2 ^ width) :
    bitsValue (canonicalBits width value) = value := by
  induction width generalizing value with
  | zero =>
    have hv : value = 0 := by simpa using h
    simp [canonicalBits, bitsValue, hv]
  | succ width ih =>
    have hdiv : value / 2 < 2 ^ width := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
      simpa only [pow_succ] using h
    rw [canonicalBits_succ, bitsValue, ih (value / 2) hdiv, bitDigit_val,
      Nat.toNat_testBit]
    simpa using Nat.mod_add_div value 2

theorem canonicalBits_field (v : F) (width : ℕ) (h : v.val < 2 ^ width) :
    bitsField (canonicalBits width v.val) = v := by
  rw [← bitsValue_cast, canonicalBits_value width v.val h]
  exact ZMod.natCast_zmod_val v

/-- An explicit complete Boolean witness, with both integer and field
reconstruction. This includes the circuit's 20-, 128- and 160-bit widths. -/
theorem num2Bits_complete (v : F) (width : ℕ) (h : v.val < 2 ^ width) :
    ∃ bs : List F, bs = canonicalBits width v.val ∧ bs.length = width ∧
      (∀ b ∈ bs, b * (b - 1) = 0) ∧ bitsValue bs = v.val ∧ bitsField bs = v := by
  exact ⟨canonicalBits width v.val, rfl, canonicalBits_length width v.val,
    canonicalBits_boolean width v.val, canonicalBits_value width v.val h,
    canonicalBits_field v width h⟩

end MSP.CircuitCompleteness
