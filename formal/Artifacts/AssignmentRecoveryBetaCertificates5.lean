import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output40 :
    normalize (substitute (BetaGatesData.output ⟨40, by decide⟩) plan.replacement) =
      normalize [(41, 1)] := by decide

theorem output41 :
    normalize (substitute (BetaGatesData.output ⟨41, by decide⟩) plan.replacement) =
      normalize [(42, 1)] := by decide

theorem output42 :
    normalize (substitute (BetaGatesData.output ⟨42, by decide⟩) plan.replacement) =
      normalize [(43, 1)] := by decide

theorem output43 :
    normalize (substitute (BetaGatesData.output ⟨43, by decide⟩) plan.replacement) =
      normalize [(44, 1)] := by decide

theorem output44 :
    normalize (substitute (BetaGatesData.output ⟨44, by decide⟩) plan.replacement) =
      normalize [(45, 1)] := by decide

theorem output45 :
    normalize (substitute (BetaGatesData.output ⟨45, by decide⟩) plan.replacement) =
      normalize [(46, 1)] := by decide

theorem output46 :
    normalize (substitute (BetaGatesData.output ⟨46, by decide⟩) plan.replacement) =
      normalize [(47, 1)] := by decide

theorem output47 :
    normalize (substitute (BetaGatesData.output ⟨47, by decide⟩) plan.replacement) =
      normalize [(48, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
