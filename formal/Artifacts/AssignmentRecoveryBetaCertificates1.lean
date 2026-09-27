import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output8 :
    normalize (substitute (BetaGatesData.output ⟨8, by decide⟩) plan.replacement) =
      normalize [(9, 1)] := by decide

theorem output9 :
    normalize (substitute (BetaGatesData.output ⟨9, by decide⟩) plan.replacement) =
      normalize [(10, 1)] := by decide

theorem output10 :
    normalize (substitute (BetaGatesData.output ⟨10, by decide⟩) plan.replacement) =
      normalize [(11, 1)] := by decide

theorem output11 :
    normalize (substitute (BetaGatesData.output ⟨11, by decide⟩) plan.replacement) =
      normalize [(12, 1)] := by decide

theorem output12 :
    normalize (substitute (BetaGatesData.output ⟨12, by decide⟩) plan.replacement) =
      normalize [(13, 1)] := by decide

theorem output13 :
    normalize (substitute (BetaGatesData.output ⟨13, by decide⟩) plan.replacement) =
      normalize [(14, 1)] := by decide

theorem output14 :
    normalize (substitute (BetaGatesData.output ⟨14, by decide⟩) plan.replacement) =
      normalize [(15, 1)] := by decide

theorem output15 :
    normalize (substitute (BetaGatesData.output ⟨15, by decide⟩) plan.replacement) =
      normalize [(16, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
