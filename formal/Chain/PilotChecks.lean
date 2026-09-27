import Chain.Pilot

/-! Kernel-checked negative controls for the pure interpreter's byte boundary,
jump scan, PUSH padding, memory expansion and frame-context behavior. -/
namespace MSP.Chain.Pilot

example : decode [0xfe] 0 = .error (.unsupportedOpcode 0xfe) := by decide
example : decode [] 0 = .ok .stop := by decide
example : validJump [0xfe, 0x5b] 1 = true := by decide
example : validJump [0x60, 0x5b] 1 = false := by decide
example : validJump [0x60, 0, 0x5b] 2 = true := by decide
example : validJump [0x61, 0x5b] 1 = false := by decide
example : pushValue [0x61, 0x12] 0 2 = 0x1200 := by decide
example : expansionCost 0 0 32 = 3 := by decide
example : expansionCost 1 0 4 = 0 := by decide

example (s : Machine P) (h : s.stack = [2]) (e : Env) (he : e.frame = none) :
    execute e .txparam s = .exceptional .outsideFrameTransaction := by
  simp [execute, h, he]

end MSP.Chain.Pilot
