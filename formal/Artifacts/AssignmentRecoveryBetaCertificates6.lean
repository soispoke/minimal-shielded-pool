import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output48 :
    normalize (substitute (BetaGatesData.output ⟨48, by decide⟩) plan.replacement) =
      normalize [(49, 1)] := by decide

theorem output49 :
    normalize (substitute (BetaGatesData.output ⟨49, by decide⟩) plan.replacement) =
      normalize [(50, 1)] := by decide

theorem output50 :
    normalize (substitute (BetaGatesData.output ⟨50, by decide⟩) plan.replacement) =
      normalize [(51, 1)] := by decide

theorem output51 :
    normalize (substitute (BetaGatesData.output ⟨51, by decide⟩) plan.replacement) =
      normalize [(52, 1)] := by decide

theorem output52 :
    normalize (substitute (BetaGatesData.output ⟨52, by decide⟩) plan.replacement) =
      normalize [(53, 1)] := by decide

theorem output53 :
    normalize (substitute (BetaGatesData.output ⟨53, by decide⟩) plan.replacement) =
      normalize [(54, 1)] := by decide

theorem output54 :
    normalize (substitute (BetaGatesData.output ⟨54, by decide⟩) plan.replacement) =
      normalize [(55, 1)] := by decide

theorem output55 :
    normalize (substitute (BetaGatesData.output ⟨55, by decide⟩) plan.replacement) =
      normalize [(56, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
