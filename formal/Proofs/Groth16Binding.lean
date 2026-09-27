import Spec.Circuit

namespace MSP

/-- Unfolding the former opaque predicate exposes all canonical proof checks
and the exact pinned key's pairing equation. No bytecode result is assumed. -/
theorem groth16_accepts_iff (bytes : List UInt8) (pub : F × F × F) :
    Groth16Accepts bytes pub ↔
      ∃ π : Groth16.ProofCoordinates,
        bytes.length = 256 ∧ Groth16.fromWords (Groth16.proofWords bytes) = π ∧
        π.Canonical ∧ π.Nonzero ∧ ∃ hc : π.OnCurve,
          ∃ hb : p • π.b.toTwistPoint hc.2.1 = 0,
            Groth16.VerificationEquation (π.a.toPoint hc.1)
              ⟨π.b.toTwistPoint hc.2.1, hb⟩ (π.c.toPoint hc.2.2) pub := by
  unfold Groth16Accepts Groth16.Accepts
  simp only [Groth16.decodeProof_eq_some_iff]
  constructor
  · rintro ⟨π, ⟨hl, he, hcan, hn⟩, hc, hb, hv⟩
    exact ⟨π, hl, he, hcan, hn, hc, hb, hv⟩
  · rintro ⟨π, hl, he, hcan, hn, hc, hb, hv⟩
    exact ⟨π, ⟨hl, he, hcan, hn⟩, hc, hb, hv⟩

theorem groth16_accepts_point_orders {bytes : List UInt8} {pub : F × F × F}
    (h : Groth16Accepts bytes pub) :
    ∃ π : Groth16.ProofCoordinates, Groth16.decodeProof bytes = some π ∧
      ∃ hc : π.OnCurve, addOrderOf (π.a.toPoint hc.1) = p ∧
        addOrderOf (π.b.toTwistPoint hc.2.1) = p ∧
        addOrderOf (π.c.toPoint hc.2.2) = p := by
  unfold Groth16Accepts at h
  exact Groth16.accepts_point_orders h

end MSP
