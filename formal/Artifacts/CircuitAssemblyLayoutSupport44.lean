import Artifacts.CircuitAssemblyLayout

namespace MSP.Artifacts.CircuitAssemblyLayout
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

/-- Every actual coefficient wire of part 44 is owned or shared. -/
theorem supported44 : ∀ c ∈ constraints 44, AssignmentAssembly.Supported (writes 44) boundary c := by
  unfold AssignmentAssembly.Supported
  decide

end MSP.Artifacts.CircuitAssemblyLayout
