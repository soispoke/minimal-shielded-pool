import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates2

/-! Exact affine recovery transport for main.spend.note[1].pk. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms51 : ∀ t : Fin 85,
    normalize (SmallHashGates.output instance51 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output2 t)
        AssignmentRecoverySmallData.wireMap51) := by decide

private theorem replacements51 : ∀ j : Fin 86,
    AssignmentRecoverySmallData.plan51.replacement
      (AssignmentRecoverySmallData.wireMap51 j.val) =
        AssignmentRecoverySmallTemplateData.plan2.replacement j.val := by decide

theorem realizes51 (ambient : Assignment) (desired : ℕ → F) (t : Fin 85) :
    eval (SmallHashGates.output instance51 t)
      (AssignmentRecoverySmallData.plan51.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan2
    AssignmentRecoverySmallData.plan51 _ _ AssignmentRecoverySmallData.wireMap51
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate2 t) (forms51 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support2 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements51 ⟨j, by change j ≤ 85 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
