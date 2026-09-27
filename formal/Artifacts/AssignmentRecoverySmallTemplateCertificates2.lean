import Artifacts.AssignmentRecoverySmallTemplateData

/-! Kernel-checked sparse inverse for shared template 2. -/

namespace MSP.Artifacts.AssignmentRecoverySmallTemplateCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmallTemplateData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem certificate2 : ∀ t : Fin 85,
    normalize (substitute (output2 t) plan2.replacement) =
      normalize [(t.val + 1, 1)] := by decide

end MSP.Artifacts.AssignmentRecoverySmallTemplateCertificates
