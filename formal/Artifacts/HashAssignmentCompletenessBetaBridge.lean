import Artifacts.HashAssignmentCompletenessBetaData

namespace MSP.Artifacts.HashAssignmentCompletenessBetaData
open BetaGates SmallHashGates MSP.Poseidon
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

theorem prefix_boundary_bridge : ∀ j : Fin 11,
    normalize (SmallHashGates.mixForms Optimized.P
      (SmallHashGates.withConstants (fullOutputForm circuit scheme.initialConstants 3)
        (Optimized.prefixConstant 3)) j) =
    normalize (BetaGates.mixForms Optimized.P
      (BetaGates.withConstants (BetaGatesData.fullOutput 3) (Optimized.prefixConstant 3)) j) := by
  decide

end MSP.Artifacts.HashAssignmentCompletenessBetaData
