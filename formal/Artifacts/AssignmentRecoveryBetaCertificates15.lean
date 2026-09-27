import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output120 :
    normalize (substitute (BetaGatesData.output ⟨120, by decide⟩) plan.replacement) =
      normalize [(121, 1)] := by decide

theorem output121 :
    normalize (substitute (BetaGatesData.output ⟨121, by decide⟩) plan.replacement) =
      normalize [(122, 1)] := by decide

theorem output122 :
    normalize (substitute (BetaGatesData.output ⟨122, by decide⟩) plan.replacement) =
      normalize [(123, 1)] := by decide

theorem output123 :
    normalize (substitute (BetaGatesData.output ⟨123, by decide⟩) plan.replacement) =
      normalize [(124, 1)] := by decide

theorem output124 :
    normalize (substitute (BetaGatesData.output ⟨124, by decide⟩) plan.replacement) =
      normalize [(125, 1)] := by decide

theorem output125 :
    normalize (substitute (BetaGatesData.output ⟨125, by decide⟩) plan.replacement) =
      normalize [(126, 1)] := by decide

theorem output126 :
    normalize (substitute (BetaGatesData.output ⟨126, by decide⟩) plan.replacement) =
      normalize [(127, 1)] := by decide

theorem output127 :
    normalize (substitute (BetaGatesData.output ⟨127, by decide⟩) plan.replacement) =
      normalize [(128, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
