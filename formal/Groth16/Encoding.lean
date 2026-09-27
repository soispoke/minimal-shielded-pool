import Groth16.Curve

/-! The strict 256-byte proof encoding of C9. This layer rejects noncanonical
coordinates and infinity encodings. Curve, subgroup and pairing checks remain
separate; successfully decoding bytes does not assert that a proof verifies. -/

namespace MSP.Groth16

abbrev ProofWords := Fin 8 → ℕ

/-- EIP-197 orders each G2 coordinate imaginary part first. -/
def fromWords (w : ProofWords) : ProofCoordinates where
  a := ⟨w 0, w 1⟩
  b := ⟨w 3, w 2, w 5, w 4⟩
  c := ⟨w 6, w 7⟩

/-- The existing canonical byte-reader is big-endian. The decoder below first
requires exactly eight complete words, so its zero-padding rule is unused. -/
def proofWords (bytes : List UInt8) : ProofWords :=
  fun i => wordAt bytes (32 * i.val)

def decodeProof (bytes : List UInt8) : Option ProofCoordinates :=
  if bytes.length = 256 then
    let π := fromWords (proofWords bytes)
    if π.Canonical ∧ π.Nonzero then some π else none
  else none

theorem decodeProof_eq_some_iff (bytes : List UInt8) (π : ProofCoordinates) :
    decodeProof bytes = some π ↔
      bytes.length = 256 ∧ fromWords (proofWords bytes) = π ∧ π.Canonical ∧ π.Nonzero := by
  by_cases hl : bytes.length = 256
  · by_cases hv : (fromWords (proofWords bytes)).Canonical ∧
        (fromWords (proofWords bytes)).Nonzero
    · simp only [decodeProof, hl, ite_true, hv, Option.some.injEq, true_and]
      constructor
      · intro h
        exact ⟨h, h ▸ hv⟩
      · exact fun h => h.1
    · simp only [decodeProof, hl, ite_true, hv, ite_false, true_and]
      constructor
      · intro h
        cases h
      · rintro ⟨he, hc, hn⟩
        exact False.elim (hv (he.symm ▸ ⟨hc, hn⟩))
  · simp [decodeProof, hl]

theorem decodeProof_length (bytes : List UInt8) (π : ProofCoordinates)
    (h : decodeProof bytes = some π) : bytes.length = 256 :=
  ((decodeProof_eq_some_iff bytes π).mp h).1

theorem decodeProof_canonical (bytes : List UInt8) (π : ProofCoordinates)
    (h : decodeProof bytes = some π) : π.Canonical :=
  ((decodeProof_eq_some_iff bytes π).mp h).2.2.1

theorem decodeProof_nonzero (bytes : List UInt8) (π : ProofCoordinates)
    (h : decodeProof bytes = some π) : π.Nonzero :=
  ((decodeProof_eq_some_iff bytes π).mp h).2.2.2

theorem fromWords_canonical (w : ProofWords) :
    (fromWords w).Canonical ↔ ∀ i, w i < q := by
  simp [ProofCoordinates.Canonical, G1Coordinates.Canonical, G2Coordinates.Canonical,
    fromWords, Fin.forall_fin_succ]
  tauto

theorem decodeProof_rejects_coordinate (bytes : List UInt8) (i : Fin 8)
    (h : q ≤ proofWords bytes i) : decodeProof bytes = none := by
  by_cases hl : bytes.length = 256
  · have hn : ¬ (fromWords (proofWords bytes)).Canonical := by
      intro hc
      have := (fromWords_canonical _).mp hc i
      omega
    simp [decodeProof, hl, hn]
  · simp [decodeProof, hl]

theorem decodeProof_rejects_infinity (bytes : List UInt8)
    (h : ¬ (fromWords (proofWords bytes)).Nonzero) : decodeProof bytes = none := by
  by_cases hl : bytes.length = 256 <;> simp [decodeProof, hl, h]

theorem decodeProof_rejects_length (bytes : List UInt8)
    (h : bytes.length ≠ 256) : decodeProof bytes = none := by
  simp [decodeProof, h]

theorem full_word_length (bytes : List UInt8) (hl : bytes.length = 256) (i : Fin 8) :
    ((bytes.drop (32 * i.val)).take 32).length = 32 := by
  simp only [List.length_take, List.length_drop, hl]
  have := i.isLt
  omega

theorem decoded_g2_order (bytes : List UInt8) (π : ProofCoordinates)
    (h : decodeProof bytes = some π) :
    π.b.xIm = proofWords bytes 2 ∧ π.b.xRe = proofWords bytes 3 ∧
    π.b.yIm = proofWords bytes 4 ∧ π.b.yRe = proofWords bytes 5 := by
  have he := ((decodeProof_eq_some_iff bytes π).mp h).2.1
  rw [← he]
  exact ⟨rfl, rfl, rfl, rfl⟩

end MSP.Groth16
