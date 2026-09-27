import Artifacts.CircuitAssemblyLayout

namespace MSP.Artifacts.CircuitAssemblyLayout
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

/-- Every actual coefficient wire of part 16 is owned or shared. -/
theorem supported16 : ∀ c ∈ constraints 16, AssignmentAssembly.Supported (writes 16) boundary c := by
  unfold AssignmentAssembly.Supported
  decide

end MSP.Artifacts.CircuitAssemblyLayout
