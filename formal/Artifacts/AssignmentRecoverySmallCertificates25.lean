import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates2

/-! Exact affine recovery transport for main.spend.note[0].pk. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms25 : ∀ t : Fin 85,
    normalize (SmallHashGates.output instance25 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output2 t)
        AssignmentRecoverySmallData.wireMap25) := by decide

private theorem replacements25 : ∀ j : Fin 86,
    AssignmentRecoverySmallData.plan25.replacement
      (AssignmentRecoverySmallData.wireMap25 j.val) =
        AssignmentRecoverySmallTemplateData.plan2.replacement j.val := by decide

theorem realizes25 (ambient : Assignment) (desired : ℕ → F) (t : Fin 85) :
    eval (SmallHashGates.output instance25 t)
      (AssignmentRecoverySmallData.plan25.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan2
    AssignmentRecoverySmallData.plan25 _ _ AssignmentRecoverySmallData.wireMap25
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate2 t) (forms25 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support2 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements25 ⟨j, by change j ≤ 85 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
