import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output96 :
    normalize (substitute (BetaGatesData.output ⟨96, by decide⟩) plan.replacement) =
      normalize [(97, 1)] := by decide

theorem output97 :
    normalize (substitute (BetaGatesData.output ⟨97, by decide⟩) plan.replacement) =
      normalize [(98, 1)] := by decide

theorem output98 :
    normalize (substitute (BetaGatesData.output ⟨98, by decide⟩) plan.replacement) =
      normalize [(99, 1)] := by decide

theorem output99 :
    normalize (substitute (BetaGatesData.output ⟨99, by decide⟩) plan.replacement) =
      normalize [(100, 1)] := by decide

theorem output100 :
    normalize (substitute (BetaGatesData.output ⟨100, by decide⟩) plan.replacement) =
      normalize [(101, 1)] := by decide

theorem output101 :
    normalize (substitute (BetaGatesData.output ⟨101, by decide⟩) plan.replacement) =
      normalize [(102, 1)] := by decide

theorem output102 :
    normalize (substitute (BetaGatesData.output ⟨102, by decide⟩) plan.replacement) =
      normalize [(103, 1)] := by decide

theorem output103 :
    normalize (substitute (BetaGatesData.output ⟨103, by decide⟩) plan.replacement) =
      normalize [(104, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
