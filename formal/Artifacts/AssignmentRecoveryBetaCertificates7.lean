import Artifacts.AssignmentRecoveryBetaData

/-! Kernel-checked substitutions of actual pinned beta output constraints. -/

namespace MSP.Artifacts.AssignmentRecoveryBetaCertificates

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output56 :
    normalize (substitute (BetaGatesData.output ⟨56, by decide⟩) plan.replacement) =
      normalize [(57, 1)] := by decide

theorem output57 :
    normalize (substitute (BetaGatesData.output ⟨57, by decide⟩) plan.replacement) =
      normalize [(58, 1)] := by decide

theorem output58 :
    normalize (substitute (BetaGatesData.output ⟨58, by decide⟩) plan.replacement) =
      normalize [(59, 1)] := by decide

theorem output59 :
    normalize (substitute (BetaGatesData.output ⟨59, by decide⟩) plan.replacement) =
      normalize [(60, 1)] := by decide

theorem output60 :
    normalize (substitute (BetaGatesData.output ⟨60, by decide⟩) plan.replacement) =
      normalize [(61, 1)] := by decide

theorem output61 :
    normalize (substitute (BetaGatesData.output ⟨61, by decide⟩) plan.replacement) =
      normalize [(62, 1)] := by decide

theorem output62 :
    normalize (substitute (BetaGatesData.output ⟨62, by decide⟩) plan.replacement) =
      normalize [(63, 1)] := by decide

theorem output63 :
    normalize (substitute (BetaGatesData.output ⟨63, by decide⟩) plan.replacement) =
      normalize [(64, 1)] := by decide

end MSP.Artifacts.AssignmentRecoveryBetaCertificates
