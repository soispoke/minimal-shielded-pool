import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output32 :
    normalize (substitute (BetaGatesData.output ⟨32, by decide⟩) plan.replacement) =
      normalize [(33, 1)] := by decide

theorem output33 :
    normalize (substitute (BetaGatesData.output ⟨33, by decide⟩) plan.replacement) =
      normalize [(34, 1)] := by decide

theorem output34 :
    normalize (substitute (BetaGatesData.output ⟨34, by decide⟩) plan.replacement) =
      normalize [(35, 1)] := by decide

theorem output35 :
    normalize (substitute (BetaGatesData.output ⟨35, by decide⟩) plan.replacement) =
      normalize [(36, 1)] := by decide

theorem output36 :
    normalize (substitute (BetaGatesData.output ⟨36, by decide⟩) plan.replacement) =
      normalize [(37, 1)] := by decide

theorem output37 :
    normalize (substitute (BetaGatesData.output ⟨37, by decide⟩) plan.replacement) =
      normalize [(38, 1)] := by decide

theorem output38 :
    normalize (substitute (BetaGatesData.output ⟨38, by decide⟩) plan.replacement) =
      normalize [(39, 1)] := by decide

theorem output39 :
    normalize (substitute (BetaGatesData.output ⟨39, by decide⟩) plan.replacement) =
      normalize [(40, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
