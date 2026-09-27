import Artifacts.HashAssignmentCompletenessPowers
import Artifacts.HashAssignmentCompletenessAffine

/-! Compose a semantic trace, disjoint physical power writes, exact affine
recovery and checked affine round certificates into an actual hash witness. -/

namespace MSP.Artifacts.HashAssignmentCompleteness

open BetaGates SmallHashGates HashTraceCompleteness AssignmentRecovery

def ambientInputs (g : Instance) (ambient : Assignment) : Fin g.arity → F :=
  fun j => eval (g.inputForms j) ambient

/-- The recovery algorithm's arbitrary-target property, later discharged by
the finite substitution certificates for each actual plan. -/
def RecoveryCorrect (g : Instance) (plan : Plan) : Prop :=
  ∀ (ambient : Assignment) (desired : ℕ → F) (t : Fin g.tripleCount),
    eval (output g t) (plan.apply ambient desired) = desired t.val

noncomputable def buildAssignment {g : Instance} (s : Scheme g.arity g.partialRounds)
    (layout : PowerLayout g) (plan : Plan) (stages : StageMap g)
    (ambient : Assignment) : Assignment :=
  assign layout plan stages (construct s (ambientInputs g ambient)) ambient

theorem buildAssignment_zero {g : Instance} (s : Scheme g.arity g.partialRounds)
    (layout : PowerLayout g) (plan : Plan) (stages : StageMap g) (ambient : Assignment) :
    buildAssignment s layout plan stages ambient 0 = ambient 0 :=
  assign_zero layout plan stages _ ambient

theorem buildAssignment_inputs {g : Instance} (s : Scheme g.arity g.partialRounds)
    (layout : PowerLayout g) (plan : Plan) (separate : WriteSeparation layout plan)
    (stages : StageMap g) (ambient : Assignment) (j : Fin g.arity) :
    eval (g.inputForms j) (buildAssignment s layout plan stages ambient) =
      eval (g.inputForms j) ambient :=
  assign_inputs layout plan separate stages _ ambient j

theorem buildAssignment_preserves {g : Instance} (s : Scheme g.arity g.partialRounds)
    (layout : PowerLayout g) (plan : Plan) (stages : StageMap g) (ambient : Assignment)
    (wire : ℕ) (hrecovery : wire ∉ plan.written) (hpowers : ∀ k, layout.wire k ≠ wire) :
    buildAssignment s layout plan stages ambient wire = ambient wire :=
  assign_preserves layout plan stages _ ambient wire hrecovery hpowers

theorem constraints_of_triples (g : Instance) (w : Assignment)
    (h : ∀ t j, (triple g t j).Holds w) : ∀ c ∈ g.constraints, c.Holds w := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hib : i < 3 * g.tripleCount := by simpa only [g.constraintCount] using hi
  let t : Fin g.tripleCount := ⟨i / 3, by omega⟩
  let j : Fin 3 := ⟨i % 3, by omega⟩
  have he : triple g t j = g.constraints[i] := by
    unfold triple
    have hi' : 3 * t.val + j.val = i := by dsimp [t, j]; omega
    simp only [hi']
  rw [← he]
  exact h t j

/-- Every constraint in the exact hash slice holds, and its physical output is
the computed hash of the ambient inputs.  The only ambient premise is wire
zero's canonical value; no circuit, hash-result or witness-existence premise
is assumed.  All remaining parameters are finite, input-independent
certificates and the proved arbitrary-target recovery algorithm. -/
theorem buildAssignment_complete {g : Instance} (s : Scheme g.arity g.partialRounds)
    (affine : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (layout : PowerLayout g) (plan : Plan) (separate : WriteSeparation layout plan)
    (stages : StageMap g) (recovery : RecoveryCorrect g plan)
    (ambient : Assignment) (hzero : ambient 0 = 1) :
    (∀ c ∈ g.constraints, c.Holds (buildAssignment s layout plan stages ambient)) ∧
    eval g.outputForm (buildAssignment s layout plan stages ambient) =
      s.hash (ambientInputs g ambient) := by
  let trace := construct s (ambientInputs g ambient)
  let w := buildAssignment s layout plan stages ambient
  have hz : w 0 = 1 := (buildAssignment_zero s layout plan stages ambient).trans hzero
  have hi : ∀ j, eval (g.inputForms j) w = ambientInputs g ambient j :=
    buildAssignment_inputs s layout plan separate stages ambient
  have ho : ∀ t, eval (output g t) w = stageOutput stages trace t := by
    intro t
    exact (recovery (layout.apply ambient (stageInput stages trace))
      (desired stages trace) t).trans (desired_at stages trace t)
  constructor
  · apply constraints_of_triples
    intro t j
    apply triple_holds t (signs t) w (stageInput stages trace t)
    · exact input_agrees affine stages trace w hz hi ho t
    · exact assign_square layout plan separate stages trace ambient t
    · exact assign_fourth layout plan separate stages trace ambient t
    · exact (ho t).trans (stageOutput_power stages trace t)
  · exact (output_agrees affine stages trace w hz hi ho).trans trace.output_hash

end MSP.Artifacts.HashAssignmentCompleteness
