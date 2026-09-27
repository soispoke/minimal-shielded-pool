import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates0

/-! Exact affine recovery transport for main.spend.note[1].node[15]. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms44 : ∀ t : Fin 80,
    normalize (SmallHashGates.output instance44 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output0 t)
        AssignmentRecoverySmallData.wireMap44) := by decide

private theorem replacements44 : ∀ j : Fin 81,
    AssignmentRecoverySmallData.plan44.replacement
      (AssignmentRecoverySmallData.wireMap44 j.val) =
        AssignmentRecoverySmallTemplateData.plan0.replacement j.val := by decide

theorem realizes44 (ambient : Assignment) (desired : ℕ → F) (t : Fin 80) :
    eval (SmallHashGates.output instance44 t)
      (AssignmentRecoverySmallData.plan44.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan0
    AssignmentRecoverySmallData.plan44 _ _ AssignmentRecoverySmallData.wireMap44
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate0 t) (forms44 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support0 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements44 ⟨j, by change j ≤ 80 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
