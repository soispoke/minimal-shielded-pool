import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output112 :
    normalize (substitute (BetaGatesData.output ⟨112, by decide⟩) plan.replacement) =
      normalize [(113, 1)] := by decide

theorem output113 :
    normalize (substitute (BetaGatesData.output ⟨113, by decide⟩) plan.replacement) =
      normalize [(114, 1)] := by decide

theorem output114 :
    normalize (substitute (BetaGatesData.output ⟨114, by decide⟩) plan.replacement) =
      normalize [(115, 1)] := by decide

theorem output115 :
    normalize (substitute (BetaGatesData.output ⟨115, by decide⟩) plan.replacement) =
      normalize [(116, 1)] := by decide

theorem output116 :
    normalize (substitute (BetaGatesData.output ⟨116, by decide⟩) plan.replacement) =
      normalize [(117, 1)] := by decide

theorem output117 :
    normalize (substitute (BetaGatesData.output ⟨117, by decide⟩) plan.replacement) =
      normalize [(118, 1)] := by decide

theorem output118 :
    normalize (substitute (BetaGatesData.output ⟨118, by decide⟩) plan.replacement) =
      normalize [(119, 1)] := by decide

theorem output119 :
    normalize (substitute (BetaGatesData.output ⟨119, by decide⟩) plan.replacement) =
      normalize [(120, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
