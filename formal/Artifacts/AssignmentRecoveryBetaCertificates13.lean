import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output104 :
    normalize (substitute (BetaGatesData.output ⟨104, by decide⟩) plan.replacement) =
      normalize [(105, 1)] := by decide

theorem output105 :
    normalize (substitute (BetaGatesData.output ⟨105, by decide⟩) plan.replacement) =
      normalize [(106, 1)] := by decide

theorem output106 :
    normalize (substitute (BetaGatesData.output ⟨106, by decide⟩) plan.replacement) =
      normalize [(107, 1)] := by decide

theorem output107 :
    normalize (substitute (BetaGatesData.output ⟨107, by decide⟩) plan.replacement) =
      normalize [(108, 1)] := by decide

theorem output108 :
    normalize (substitute (BetaGatesData.output ⟨108, by decide⟩) plan.replacement) =
      normalize [(109, 1)] := by decide

theorem output109 :
    normalize (substitute (BetaGatesData.output ⟨109, by decide⟩) plan.replacement) =
      normalize [(110, 1)] := by decide

theorem output110 :
    normalize (substitute (BetaGatesData.output ⟨110, by decide⟩) plan.replacement) =
      normalize [(111, 1)] := by decide

theorem output111 :
    normalize (substitute (BetaGatesData.output ⟨111, by decide⟩) plan.replacement) =
      normalize [(112, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
