import Artifacts.CircuitAssemblyLayout

namespace MSP.Artifacts.CircuitAssemblyLayout
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

/-- Every actual coefficient wire of part 33 is owned or shared. -/
theorem supported33 : ∀ c ∈ constraints 33, AssignmentAssembly.Supported (writes 33) boundary c := by
  unfold AssignmentAssembly.Supported
  decide

end MSP.Artifacts.CircuitAssemblyLayout
