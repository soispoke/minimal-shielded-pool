import Artifacts.SmallHashGatesAffineData12

/-! Kernel-checked affine schedule for main.spend.note[0].node[9]. -/

namespace MSP.Artifacts.SmallHashGatesAffineCertificates

open SmallHashGates SmallHashGatesData SmallHashGatesAffineData

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def affine12 : AffineCertificates instance12 scheme3 where
  partialStates := partialStates12
  initial := by decide
  prefixSteps := by decide
  prefixBoundary := by decide
  partialInputs := by decide
  partialSteps := by decide
  partialBoundary := by decide
  suffixSteps := by decide
  finalMix := by decide

end MSP.Artifacts.SmallHashGatesAffineCertificates
