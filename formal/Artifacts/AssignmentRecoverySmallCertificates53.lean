import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates1

/-! Exact affine recovery transport for main.spend.outCm[1]. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms53 : ∀ t : Fin 86,
    normalize (SmallHashGates.output instance53 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output1 t)
        AssignmentRecoverySmallData.wireMap53) := by decide

private theorem replacements53 : ∀ j : Fin 87,
    AssignmentRecoverySmallData.plan53.replacement
      (AssignmentRecoverySmallData.wireMap53 j.val) =
        AssignmentRecoverySmallTemplateData.plan1.replacement j.val := by decide

theorem realizes53 (ambient : Assignment) (desired : ℕ → F) (t : Fin 86) :
    eval (SmallHashGates.output instance53 t)
      (AssignmentRecoverySmallData.plan53.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan1
    AssignmentRecoverySmallData.plan53 _ _ AssignmentRecoverySmallData.wireMap53
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate1 t) (forms53 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support1 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements53 ⟨j, by change j ≤ 86 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
