import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates0

/-! Exact affine recovery transport for main.spend.note[0].domainKey. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms0 : ∀ t : Fin 80,
    normalize (SmallHashGates.output instance0 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output0 t)
        AssignmentRecoverySmallData.wireMap0) := by decide

private theorem replacements0 : ∀ j : Fin 81,
    AssignmentRecoverySmallData.plan0.replacement
      (AssignmentRecoverySmallData.wireMap0 j.val) =
        AssignmentRecoverySmallTemplateData.plan0.replacement j.val := by decide

theorem realizes0 (ambient : Assignment) (desired : ℕ → F) (t : Fin 80) :
    eval (SmallHashGates.output instance0 t)
      (AssignmentRecoverySmallData.plan0.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan0
    AssignmentRecoverySmallData.plan0 _ _ AssignmentRecoverySmallData.wireMap0
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate0 t) (forms0 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support0 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements0 ⟨j, by change j ≤ 80 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
