import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output128 :
    normalize (substitute (BetaGatesData.output ⟨128, by decide⟩) plan.replacement) =
      normalize [(129, 1)] := by decide

theorem output129 :
    normalize (substitute (BetaGatesData.output ⟨129, by decide⟩) plan.replacement) =
      normalize [(130, 1)] := by decide

theorem output130 :
    normalize (substitute (BetaGatesData.output ⟨130, by decide⟩) plan.replacement) =
      normalize [(131, 1)] := by decide

theorem output131 :
    normalize (substitute (BetaGatesData.output ⟨131, by decide⟩) plan.replacement) =
      normalize [(132, 1)] := by decide

theorem output132 :
    normalize (substitute (BetaGatesData.output ⟨132, by decide⟩) plan.replacement) =
      normalize [(133, 1)] := by decide

theorem output133 :
    normalize (substitute (BetaGatesData.output ⟨133, by decide⟩) plan.replacement) =
      normalize [(134, 1)] := by decide

theorem output134 :
    normalize (substitute (BetaGatesData.output ⟨134, by decide⟩) plan.replacement) =
      normalize [(135, 1)] := by decide

theorem output135 :
    normalize (substitute (BetaGatesData.output ⟨135, by decide⟩) plan.replacement) =
      normalize [(136, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
