import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output0 :
    normalize (substitute (BetaGatesData.output ⟨0, by decide⟩) plan.replacement) =
      normalize [(1, 1)] := by decide

theorem output1 :
    normalize (substitute (BetaGatesData.output ⟨1, by decide⟩) plan.replacement) =
      normalize [(2, 1)] := by decide

theorem output2 :
    normalize (substitute (BetaGatesData.output ⟨2, by decide⟩) plan.replacement) =
      normalize [(3, 1)] := by decide

theorem output3 :
    normalize (substitute (BetaGatesData.output ⟨3, by decide⟩) plan.replacement) =
      normalize [(4, 1)] := by decide

theorem output4 :
    normalize (substitute (BetaGatesData.output ⟨4, by decide⟩) plan.replacement) =
      normalize [(5, 1)] := by decide

theorem output5 :
    normalize (substitute (BetaGatesData.output ⟨5, by decide⟩) plan.replacement) =
      normalize [(6, 1)] := by decide

theorem output6 :
    normalize (substitute (BetaGatesData.output ⟨6, by decide⟩) plan.replacement) =
      normalize [(7, 1)] := by decide

theorem output7 :
    normalize (substitute (BetaGatesData.output ⟨7, by decide⟩) plan.replacement) =
      normalize [(8, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
