import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output88 :
    normalize (substitute (BetaGatesData.output ⟨88, by decide⟩) plan.replacement) =
      normalize [(89, 1)] := by decide

theorem output89 :
    normalize (substitute (BetaGatesData.output ⟨89, by decide⟩) plan.replacement) =
      normalize [(90, 1)] := by decide

theorem output90 :
    normalize (substitute (BetaGatesData.output ⟨90, by decide⟩) plan.replacement) =
      normalize [(91, 1)] := by decide

theorem output91 :
    normalize (substitute (BetaGatesData.output ⟨91, by decide⟩) plan.replacement) =
      normalize [(92, 1)] := by decide

theorem output92 :
    normalize (substitute (BetaGatesData.output ⟨92, by decide⟩) plan.replacement) =
      normalize [(93, 1)] := by decide

theorem output93 :
    normalize (substitute (BetaGatesData.output ⟨93, by decide⟩) plan.replacement) =
      normalize [(94, 1)] := by decide

theorem output94 :
    normalize (substitute (BetaGatesData.output ⟨94, by decide⟩) plan.replacement) =
      normalize [(95, 1)] := by decide

theorem output95 :
    normalize (substitute (BetaGatesData.output ⟨95, by decide⟩) plan.replacement) =
      normalize [(96, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
