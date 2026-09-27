import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output80 :
    normalize (substitute (BetaGatesData.output ⟨80, by decide⟩) plan.replacement) =
      normalize [(81, 1)] := by decide

theorem output81 :
    normalize (substitute (BetaGatesData.output ⟨81, by decide⟩) plan.replacement) =
      normalize [(82, 1)] := by decide

theorem output82 :
    normalize (substitute (BetaGatesData.output ⟨82, by decide⟩) plan.replacement) =
      normalize [(83, 1)] := by decide

theorem output83 :
    normalize (substitute (BetaGatesData.output ⟨83, by decide⟩) plan.replacement) =
      normalize [(84, 1)] := by decide

theorem output84 :
    normalize (substitute (BetaGatesData.output ⟨84, by decide⟩) plan.replacement) =
      normalize [(85, 1)] := by decide

theorem output85 :
    normalize (substitute (BetaGatesData.output ⟨85, by decide⟩) plan.replacement) =
      normalize [(86, 1)] := by decide

theorem output86 :
    normalize (substitute (BetaGatesData.output ⟨86, by decide⟩) plan.replacement) =
      normalize [(87, 1)] := by decide

theorem output87 :
    normalize (substitute (BetaGatesData.output ⟨87, by decide⟩) plan.replacement) =
      normalize [(88, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
