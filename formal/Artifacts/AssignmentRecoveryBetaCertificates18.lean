import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output144 :
    normalize (substitute (BetaGatesData.output ⟨144, by decide⟩) plan.replacement) =
      normalize [(145, 1)] := by decide

theorem output145 :
    normalize (substitute (BetaGatesData.output ⟨145, by decide⟩) plan.replacement) =
      normalize [(146, 1)] := by decide

theorem output146 :
    normalize (substitute (BetaGatesData.output ⟨146, by decide⟩) plan.replacement) =
      normalize [(147, 1)] := by decide

theorem output147 :
    normalize (substitute (BetaGatesData.output ⟨147, by decide⟩) plan.replacement) =
      normalize [(148, 1)] := by decide

theorem output148 :
    normalize (substitute (BetaGatesData.output ⟨148, by decide⟩) plan.replacement) =
      normalize [(149, 1)] := by decide

theorem output149 :
    normalize (substitute (BetaGatesData.output ⟨149, by decide⟩) plan.replacement) =
      normalize [(150, 1)] := by decide

theorem output150 :
    normalize (substitute (BetaGatesData.output ⟨150, by decide⟩) plan.replacement) =
      normalize [(151, 1)] := by decide

theorem output151 :
    normalize (substitute (BetaGatesData.output ⟨151, by decide⟩) plan.replacement) =
      normalize [(152, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
