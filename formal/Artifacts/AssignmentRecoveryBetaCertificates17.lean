import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output136 :
    normalize (substitute (BetaGatesData.output ⟨136, by decide⟩) plan.replacement) =
      normalize [(137, 1)] := by decide

theorem output137 :
    normalize (substitute (BetaGatesData.output ⟨137, by decide⟩) plan.replacement) =
      normalize [(138, 1)] := by decide

theorem output138 :
    normalize (substitute (BetaGatesData.output ⟨138, by decide⟩) plan.replacement) =
      normalize [(139, 1)] := by decide

theorem output139 :
    normalize (substitute (BetaGatesData.output ⟨139, by decide⟩) plan.replacement) =
      normalize [(140, 1)] := by decide

theorem output140 :
    normalize (substitute (BetaGatesData.output ⟨140, by decide⟩) plan.replacement) =
      normalize [(141, 1)] := by decide

theorem output141 :
    normalize (substitute (BetaGatesData.output ⟨141, by decide⟩) plan.replacement) =
      normalize [(142, 1)] := by decide

theorem output142 :
    normalize (substitute (BetaGatesData.output ⟨142, by decide⟩) plan.replacement) =
      normalize [(143, 1)] := by decide

theorem output143 :
    normalize (substitute (BetaGatesData.output ⟨143, by decide⟩) plan.replacement) =
      normalize [(144, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
