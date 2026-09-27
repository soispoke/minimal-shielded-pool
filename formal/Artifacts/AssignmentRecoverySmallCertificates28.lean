import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates1

/-! Exact affine recovery transport for main.spend.note[1].leaf. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms28 : ∀ t : Fin 86,
    normalize (SmallHashGates.output instance28 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output1 t)
        AssignmentRecoverySmallData.wireMap28) := by decide

private theorem replacements28 : ∀ j : Fin 87,
    AssignmentRecoverySmallData.plan28.replacement
      (AssignmentRecoverySmallData.wireMap28 j.val) =
        AssignmentRecoverySmallTemplateData.plan1.replacement j.val := by decide

theorem realizes28 (ambient : Assignment) (desired : ℕ → F) (t : Fin 86) :
    eval (SmallHashGates.output instance28 t)
      (AssignmentRecoverySmallData.plan28.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan1
    AssignmentRecoverySmallData.plan28 _ _ AssignmentRecoverySmallData.wireMap28
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate1 t) (forms28 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support1 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements28 ⟨j, by change j ≤ 86 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
