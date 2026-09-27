import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output64 :
    normalize (substitute (BetaGatesData.output ⟨64, by decide⟩) plan.replacement) =
      normalize [(65, 1)] := by decide

theorem output65 :
    normalize (substitute (BetaGatesData.output ⟨65, by decide⟩) plan.replacement) =
      normalize [(66, 1)] := by decide

theorem output66 :
    normalize (substitute (BetaGatesData.output ⟨66, by decide⟩) plan.replacement) =
      normalize [(67, 1)] := by decide

theorem output67 :
    normalize (substitute (BetaGatesData.output ⟨67, by decide⟩) plan.replacement) =
      normalize [(68, 1)] := by decide

theorem output68 :
    normalize (substitute (BetaGatesData.output ⟨68, by decide⟩) plan.replacement) =
      normalize [(69, 1)] := by decide

theorem output69 :
    normalize (substitute (BetaGatesData.output ⟨69, by decide⟩) plan.replacement) =
      normalize [(70, 1)] := by decide

theorem output70 :
    normalize (substitute (BetaGatesData.output ⟨70, by decide⟩) plan.replacement) =
      normalize [(71, 1)] := by decide

theorem output71 :
    normalize (substitute (BetaGatesData.output ⟨71, by decide⟩) plan.replacement) =
      normalize [(72, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
