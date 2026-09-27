import Artifacts.HashTraceCompleteness

/-! The inverse of the actual compiler-retained S-box stage inventory.  The
finite identities are checked for each instance; they contain no hash results. -/

namespace MSP.Artifacts.HashAssignmentCompleteness

open SmallHashGates HashTraceCompleteness

abbrev Stage (g : Instance) :=
  Sum (Fin 8 × Fin (g.arity + 1)) (Fin g.partialRounds)

structure StageMap (g : Instance) where
  atStage : Fin g.tripleCount → Stage g
  full : ∀ r j t, g.fullStage r j = some t → atStage t = .inl (r, j)
  partial_eq : ∀ r, atStage (g.partialStage r) = .inr r
  valid : ∀ t, match atStage t with
    | .inl (r, j) => g.fullStage r j = some t
    | .inr r => g.partialStage r = t

def stageInput {g : Instance} {s : Scheme g.arity g.partialRounds}
    {inputs : Fin g.arity → F} (stages : StageMap g) (trace : Trace s inputs)
    (t : Fin g.tripleCount) : F :=
  match stages.atStage t with
  | .inl (r, j) => trace.fullInput r j
  | .inr r => trace.partialState r.castSucc 0

def stageOutput {g : Instance} {s : Scheme g.arity g.partialRounds}
    {inputs : Fin g.arity → F} (stages : StageMap g) (trace : Trace s inputs)
    (t : Fin g.tripleCount) : F :=
  match stages.atStage t with
  | .inl (r, j) => trace.fullOutput r j
  | .inr r => trace.partialOutput r

theorem stageOutput_power {g : Instance} {s : Scheme g.arity g.partialRounds}
    {inputs : Fin g.arity → F} (stages : StageMap g) (trace : Trace s inputs)
    (t : Fin g.tripleCount) : stageOutput stages trace t = (stageInput stages trace t)^5 := by
  unfold stageOutput stageInput
  cases stages.atStage t with
  | inl rj => exact trace.fullSbox rj.1 rj.2
  | inr r => exact trace.partialSbox r

/-- Total target vector consumed by the affine recovery API. -/
def desired {g : Instance} {s : Scheme g.arity g.partialRounds}
    {inputs : Fin g.arity → F} (stages : StageMap g) (trace : Trace s inputs) (i : ℕ) : F :=
  if hi : i < g.tripleCount then stageOutput stages trace ⟨i, hi⟩ else 0

theorem desired_at {g : Instance} {s : Scheme g.arity g.partialRounds}
    {inputs : Fin g.arity → F} (stages : StageMap g) (trace : Trace s inputs)
    (t : Fin g.tripleCount) : desired stages trace t.val = stageOutput stages trace t := by
  simp only [desired, t.isLt, ↓reduceDIte]

end MSP.Artifacts.HashAssignmentCompleteness
