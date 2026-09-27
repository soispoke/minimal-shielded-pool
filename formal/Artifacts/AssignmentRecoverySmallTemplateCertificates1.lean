import Artifacts.AssignmentRecoverySmallTemplateData

/-! Kernel-checked sparse inverse for shared template 1. -/

namespace MSP.Artifacts.AssignmentRecoverySmallTemplateCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmallTemplateData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem certificate1 : ∀ t : Fin 86,
    normalize (substitute (output1 t) plan1.replacement) =
      normalize [(t.val + 1, 1)] := by decide

end MSP.Artifacts.AssignmentRecoverySmallTemplateCertificates
