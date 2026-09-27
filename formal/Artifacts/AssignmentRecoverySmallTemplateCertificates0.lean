import Artifacts.AssignmentRecoverySmallTemplateData

/-! Kernel-checked sparse inverse for shared template 0. -/

namespace MSP.Artifacts.AssignmentRecoverySmallTemplateCertificates

open BetaGates AssignmentRecovery AssignmentRecoverySmallTemplateData
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem certificate0 : ∀ t : Fin 80,
    normalize (substitute (output0 t) plan0.replacement) =
      normalize [(t.val + 1, 1)] := by decide

end MSP.Artifacts.AssignmentRecoverySmallTemplateCertificates
