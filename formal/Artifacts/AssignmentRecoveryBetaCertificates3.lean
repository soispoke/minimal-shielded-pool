import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output24 :
    normalize (substitute (BetaGatesData.output ⟨24, by decide⟩) plan.replacement) =
      normalize [(25, 1)] := by decide

theorem output25 :
    normalize (substitute (BetaGatesData.output ⟨25, by decide⟩) plan.replacement) =
      normalize [(26, 1)] := by decide

theorem output26 :
    normalize (substitute (BetaGatesData.output ⟨26, by decide⟩) plan.replacement) =
      normalize [(27, 1)] := by decide

theorem output27 :
    normalize (substitute (BetaGatesData.output ⟨27, by decide⟩) plan.replacement) =
      normalize [(28, 1)] := by decide

theorem output28 :
    normalize (substitute (BetaGatesData.output ⟨28, by decide⟩) plan.replacement) =
      normalize [(29, 1)] := by decide

theorem output29 :
    normalize (substitute (BetaGatesData.output ⟨29, by decide⟩) plan.replacement) =
      normalize [(30, 1)] := by decide

theorem output30 :
    normalize (substitute (BetaGatesData.output ⟨30, by decide⟩) plan.replacement) =
      normalize [(31, 1)] := by decide

theorem output31 :
    normalize (substitute (BetaGatesData.output ⟨31, by decide⟩) plan.replacement) =
      normalize [(32, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
