import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output152 :
    normalize (substitute (BetaGatesData.output ⟨152, by decide⟩) plan.replacement) =
      normalize [(153, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
