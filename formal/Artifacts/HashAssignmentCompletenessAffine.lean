import Artifacts.HashAssignmentCompletenessStage

/-! Constructive affine trace agreement. Realizing retained S-box outputs and
interface inputs determines all inputs and the hash output through the pinned
coefficient certificates. No constraint satisfaction is assumed. -/
namespace MSP.Artifacts.HashAssignmentCompleteness
open SmallHashGates HashTraceCompleteness
open BetaGates (eval eval_append eval_constant eval_certificate)
set_option maxHeartbeats 2000000
variable {g : Instance} {s : Scheme g.arity g.partialRounds}
    {inputs : Fin g.arity → F}

private theorem full_output (stages : StageMap g) (trace : Trace s inputs)
    (a : Assignment) (hz : a 0 = 1)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (r : Fin 8)
    (hi : evalState (fullInputForm g s.initialConstants r) a = trace.fullInput r) :
    evalState (fullOutputForm g s.initialConstants r) a = trace.fullOutput r := by
  funext j
  cases hs : g.fullStage r j with
  | some t =>
    change eval (fullOutputForm g s.initialConstants r j) a = _
    simp only [fullOutputForm, hs]
    rw [ho]
    simp only [stageOutput, stages.full r j t hs]
  | none =>
    have heq := congrFun hi j
    change eval (fullInputForm g s.initialConstants r j) a = _ at heq
    simp only [fullInputForm, hs] at heq
    change eval (fullOutputForm g s.initialConstants r j) a = _
    simp only [fullOutputForm, hs]
    rw [folded_sbox _ a hz, heq, trace.fullSbox]

private theorem partial_output (stages : StageMap g) (trace : Trace s inputs)
    (a : Assignment)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (r : Fin g.partialRounds) :
    eval (partialOutputForm g r) a = trace.partialOutput r := by
  rw [partialOutputForm, ho]
  simp only [stageOutput, stages.partial_eq]

private theorem initial_agrees (c : AffineCertificates g s) (trace : Trace s inputs)
    (a : Assignment) (hz : a 0 = 1)
    (hi : ∀ j, eval (g.inputForms j) a = inputs j) :
    evalState (fullInputForm g s.initialConstants 0) a = trace.fullInput 0 := by
  rw [trace.initial, state_certificate _ _ c.initial]
  funext j
  simp only [evalState, initialForms, eval_append, eval_constant _ _ hz, Scheme.initialState]
  split
  · simp [eval]
  · rw [hi]

private theorem prefix_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (r : Fin 3)
    (hi : evalState (fullInputForm g s.initialConstants ⟨r.val, by omega⟩) a =
      trace.fullInput ⟨r.val, by omega⟩) :
    evalState (fullInputForm g s.initialConstants ⟨r.val+1, by omega⟩) a =
      trace.fullInput ⟨r.val+1, by omega⟩ := by
  rw [state_certificate _ _ (c.prefixSteps r), eval_mixForms,
    eval_withConstants _ _ _ hz, full_output stages trace a hz ho _ hi]
  exact (trace.prefixSteps r).symm

private theorem prefix_boundary_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (hi : evalState (fullInputForm g s.initialConstants 3) a = trace.fullInput 3) :
    evalState (c.partialStates 0) a = trace.partialState 0 := by
  rw [state_certificate _ _ c.prefixBoundary, eval_mixForms,
    eval_withConstants _ _ _ hz, full_output stages trace a hz ho _ hi]
  exact trace.prefixBoundary.symm

private theorem partial_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (hstart : evalState (c.partialStates 0) a = trace.partialState 0)
    (r : Fin (g.partialRounds+1)) :
    evalState (c.partialStates r) a = trace.partialState r := by
  induction r using Fin.induction with
  | zero => exact hstart
  | succ r ih =>
    rw [state_certificate _ _ (c.partialSteps r), eval_mixForms]
    rw [trace.partialSteps]
    congr 1
    funext j
    by_cases hj : j = 0
    · subst j
      simp only [evalState, ↓reduceIte, eval_append, eval_constant _ _ hz,
        partial_output stages trace a ho]
    · simp only [evalState, if_neg hj]
      exact congrFun ih j

private theorem suffix_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (r : Fin 3)
    (hi : evalState (fullInputForm g s.initialConstants ⟨r.val+4, by omega⟩) a =
      trace.fullInput ⟨r.val+4, by omega⟩) :
    evalState (fullInputForm g s.initialConstants ⟨r.val+5, by omega⟩) a =
      trace.fullInput ⟨r.val+5, by omega⟩ := by
  rw [state_certificate _ _ (c.suffixSteps r), eval_mixForms,
    eval_withConstants _ _ _ hz, full_output stages trace a hz ho _ hi]
  exact (trace.suffixSteps r).symm

/-- Every physical affine state agrees with the explicit semantic trace. -/
theorem affine_trace_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (hi : ∀ j, eval (g.inputForms j) a = inputs j)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t) :
    (∀ r, evalState (fullInputForm g s.initialConstants r) a = trace.fullInput r) ∧
    (∀ r, evalState (c.partialStates r) a = trace.partialState r) := by
  have h0 := initial_agrees c trace a hz hi
  have h1 := prefix_agrees c stages trace a hz ho 0 h0
  have h2 := prefix_agrees c stages trace a hz ho 1 h1
  have h3 := prefix_agrees c stages trace a hz ho 2 h2
  have hp0 := prefix_boundary_agrees c stages trace a hz ho h3
  have hp := partial_agrees c stages trace a hz ho hp0
  have h4 : evalState (fullInputForm g s.initialConstants 4) a = trace.fullInput 4 := by
    rw [state_certificate _ _ c.partialBoundary, hp, trace.partialBoundary]
  have h5 := suffix_agrees c stages trace a hz ho 0 h4
  have h6 := suffix_agrees c stages trace a hz ho 1 h5
  have h7 := suffix_agrees c stages trace a hz ho 2 h6
  refine ⟨?_, hp⟩
  intro r
  fin_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- Every actual retained S-box input has its trace value. -/
theorem input_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (hi : ∀ j, eval (g.inputForms j) a = inputs j)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t)
    (t : Fin g.tripleCount) : eval (input g t) a = stageInput stages trace t := by
  obtain ⟨hf, hp⟩ := affine_trace_agrees c stages trace a hz hi ho
  have hv := stages.valid t
  cases hs : stages.atStage t with
  | inl rj =>
    simp only [hs] at hv
    have heq := congrFun (hf rj.1) rj.2
    simpa only [evalState, fullInputForm, hv, stageInput, hs] using heq
  | inr r =>
    simp only [hs] at hv
    rw [stageInput, hs]
    rw [← hv]
    have heq := congrFun (hp r.castSucc) 0
    change eval (c.partialStates r.castSucc 0) a = _ at heq
    rw [eval_certificate _ _ (c.partialInputs r) a] at heq
    exact heq

/-- The physical hash output equals the trace's computed result. -/
theorem output_agrees (c : AffineCertificates g s) (stages : StageMap g)
    (trace : Trace s inputs) (a : Assignment) (hz : a 0 = 1)
    (hi : ∀ j, eval (g.inputForms j) a = inputs j)
    (ho : ∀ t, eval (output g t) a = stageOutput stages trace t) :
    eval g.outputForm a = trace.output := by
  have hf := (affine_trace_agrees c stages trace a hz hi ho).1 7
  have e := eval_certificate _ _ c.finalMix a
  change _ = evalState (mixForms s.mds (fullOutputForm g s.initialConstants 7)) a 0 at e
  rw [eval_mixForms, full_output stages trace a hz ho 7 hf] at e
  exact e.trans trace.finalMix.symm

#print axioms input_agrees
#print axioms output_agrees
end MSP.Artifacts.HashAssignmentCompleteness
