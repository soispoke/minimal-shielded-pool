import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates1

/-! Exact affine recovery transport for main.spend.note[1].null. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms49 : ∀ t : Fin 86,
    normalize (SmallHashGates.output instance49 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output1 t)
        AssignmentRecoverySmallData.wireMap49) := by decide

private theorem replacements49 : ∀ j : Fin 87,
    AssignmentRecoverySmallData.plan49.replacement
      (AssignmentRecoverySmallData.wireMap49 j.val) =
        AssignmentRecoverySmallTemplateData.plan1.replacement j.val := by decide

theorem realizes49 (ambient : Assignment) (desired : ℕ → F) (t : Fin 86) :
    eval (SmallHashGates.output instance49 t)
      (AssignmentRecoverySmallData.plan49.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan1
    AssignmentRecoverySmallData.plan49 _ _ AssignmentRecoverySmallData.wireMap49
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate1 t) (forms49 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support1 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements49 ⟨j, by change j ≤ 86 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
