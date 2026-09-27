import Artifacts.AssignmentRecoverySmallData
import Artifacts.AssignmentRecoverySmallTemplateCertificates1

/-! Exact affine recovery transport for main.spend.outCm[0]. -/

namespace MSP.Artifacts.AssignmentRecoverySmallCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmall SmallHashGatesData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

private theorem forms52 : ∀ t : Fin 86,
    normalize (SmallHashGates.output instance52 t) =
      normalize (rename (AssignmentRecoverySmallTemplateData.output1 t)
        AssignmentRecoverySmallData.wireMap52) := by decide

private theorem replacements52 : ∀ j : Fin 87,
    AssignmentRecoverySmallData.plan52.replacement
      (AssignmentRecoverySmallData.wireMap52 j.val) =
        AssignmentRecoverySmallTemplateData.plan1.replacement j.val := by decide

theorem realizes52 (ambient : Assignment) (desired : ℕ → F) (t : Fin 86) :
    eval (SmallHashGates.output instance52 t)
      (AssignmentRecoverySmallData.plan52.apply ambient desired) = desired t.val := by
  apply realizes_renamed AssignmentRecoverySmallTemplateData.plan1
    AssignmentRecoverySmallData.plan52 _ _ AssignmentRecoverySmallData.wireMap52
    t.val t.isLt rfl
    (AssignmentRecoverySmallTemplateCertificates.certificate1 t) (forms52 t)
  · intro term hterm
    have hs := AssignmentRecoverySmallTemplateData.support1 t
    simp only [List.all_eq_true, decide_eq_true_eq] at hs
    exact hs term hterm
  · intro j hj
    exact replacements52 ⟨j, by change j ≤ 86 at hj; omega⟩

end MSP.Artifacts.AssignmentRecoverySmallCertificates
