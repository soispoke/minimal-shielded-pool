import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output16 :
    normalize (substitute (BetaGatesData.output ⟨16, by decide⟩) plan.replacement) =
      normalize [(17, 1)] := by decide

theorem output17 :
    normalize (substitute (BetaGatesData.output ⟨17, by decide⟩) plan.replacement) =
      normalize [(18, 1)] := by decide

theorem output18 :
    normalize (substitute (BetaGatesData.output ⟨18, by decide⟩) plan.replacement) =
      normalize [(19, 1)] := by decide

theorem output19 :
    normalize (substitute (BetaGatesData.output ⟨19, by decide⟩) plan.replacement) =
      normalize [(20, 1)] := by decide

theorem output20 :
    normalize (substitute (BetaGatesData.output ⟨20, by decide⟩) plan.replacement) =
      normalize [(21, 1)] := by decide

theorem output21 :
    normalize (substitute (BetaGatesData.output ⟨21, by decide⟩) plan.replacement) =
      normalize [(22, 1)] := by decide

theorem output22 :
    normalize (substitute (BetaGatesData.output ⟨22, by decide⟩) plan.replacement) =
      normalize [(23, 1)] := by decide

theorem output23 :
    normalize (substitute (BetaGatesData.output ⟨23, by decide⟩) plan.replacement) =
      normalize [(24, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
