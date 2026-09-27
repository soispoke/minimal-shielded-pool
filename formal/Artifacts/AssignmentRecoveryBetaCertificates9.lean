import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output72 :
    normalize (substitute (BetaGatesData.output ⟨72, by decide⟩) plan.replacement) =
      normalize [(73, 1)] := by decide

theorem output73 :
    normalize (substitute (BetaGatesData.output ⟨73, by decide⟩) plan.replacement) =
      normalize [(74, 1)] := by decide

theorem output74 :
    normalize (substitute (BetaGatesData.output ⟨74, by decide⟩) plan.replacement) =
      normalize [(75, 1)] := by decide

theorem output75 :
    normalize (substitute (BetaGatesData.output ⟨75, by decide⟩) plan.replacement) =
      normalize [(76, 1)] := by decide

theorem output76 :
    normalize (substitute (BetaGatesData.output ⟨76, by decide⟩) plan.replacement) =
      normalize [(77, 1)] := by decide

theorem output77 :
    normalize (substitute (BetaGatesData.output ⟨77, by decide⟩) plan.replacement) =
      normalize [(78, 1)] := by decide

theorem output78 :
    normalize (substitute (BetaGatesData.output ⟨78, by decide⟩) plan.replacement) =
      normalize [(79, 1)] := by decide

theorem output79 :
    normalize (substitute (BetaGatesData.output ⟨79, by decide⟩) plan.replacement) =
      normalize [(80, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
