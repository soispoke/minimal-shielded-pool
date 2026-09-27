import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates0

/-! Exact affine recovery transport for main.spend.note[0].node[9]. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms12 : ∀ t : Fin 80,
    normalize (SmallHashGates.output instance12 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output0 t)
        AssignmentRecoverySmallData.wireMap12) := by decide

private theorem replacements12 : ∀ j : Fin 81,
    AssignmentRecoverySmallData.plan12.replacement
      (AssignmentRecoverySmallData.wireMap12 j.val) =
        AssignmentRecoverySmallTemplateData.plan0.replacement j.val := by decide

theorem realizes12 (ambient : Assignment) (desired : ℕ → F) (t : Fin 80) :
    eval (SmallHashGates.output instance12 t)
      (AssignmentRecoverySmallData.plan12.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan0
    AssignmentRecoverySmallData.plan12 _ _ AssignmentRecoverySmallData.wireMap12
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate0 t) (forms12 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support0 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements12 ⟨j, by change j ≤ 80 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
