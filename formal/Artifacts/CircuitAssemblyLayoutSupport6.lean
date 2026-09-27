import Artifacts.CircuitAssemblyLayout

namespace MSP.Artifacts.CircuitAssemblyLayout
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

/-- Every actual coefficient wire of part 6 is owned or shared. -/
theorem supported6 : ∀ c ∈ constraints 6, AssignmentAssembly.Supported (writes 6) boundary c := by
  unfold AssignmentAssembly.Supported
  decide

end MSP.Artifacts.CircuitAssemblyLayout
