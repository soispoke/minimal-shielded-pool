import Artifacts.SmallHashGatesAffineData25

/-! Kernel-checked affine schedule for main.spend.note[0].pk. -/

namespace MSP.Artifacts.SmallHashGatesAffineCertificates

open SmallHashGates SmallHashGatesData SmallHashGatesAffineData

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def affine25 : AffineCertificates instance25 scheme4 where
  partialStates := partialStates25
  initial := by decide
  prefixSteps := by decide
  prefixBoundary := by decide
  partialInputs := by decide
  partialSteps := by decide
  partialBoundary := by decide
  suffixSteps := by decide
  finalMix := by decide

end MSP.Artifacts.SmallHashGatesAffineCertificates
