import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates1

/-! Exact affine recovery transport for main.spend.note[0].null. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms23 : ∀ t : Fin 86,
    normalize (SmallHashGates.output instance23 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output1 t)
        AssignmentRecoverySmallData.wireMap23) := by decide

private theorem replacements23 : ∀ j : Fin 87,
    AssignmentRecoverySmallData.plan23.replacement
      (AssignmentRecoverySmallData.wireMap23 j.val) =
        AssignmentRecoverySmallTemplateData.plan1.replacement j.val := by decide

theorem realizes23 (ambient : Assignment) (desired : ℕ → F) (t : Fin 86) :
    eval (SmallHashGates.output instance23 t)
      (AssignmentRecoverySmallData.plan23.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan1
    AssignmentRecoverySmallData.plan23 _ _ AssignmentRecoverySmallData.wireMap23
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate1 t) (forms23 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support1 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements23 ⟨j, by change j ≤ 86 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
