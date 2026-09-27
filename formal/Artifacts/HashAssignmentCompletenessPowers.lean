import Artifacts.HashAssignmentCompletenessStage
import Artifacts.AssignmentRecovery

/-! Construct the two retained power wires in each actual x^5 triple, then
recover its affine output wires.  Explicit write-set certificates keep the two
constructions disjoint and preserve the hash's ambient input forms. -/

namespace MSP.Artifacts.HashAssignmentCompleteness

open BetaGates SmallHashGates HashTraceCompleteness AssignmentRecovery

structure PowerLayout (g : Instance) where
  wire : Fin g.tripleCount × Fin 2 → ℕ
  injective : Function.Injective wire
  nonzero : ∀ k, wire k ≠ 0
  square : ∀ t, normalize (ofLC (triple g t 1).b) = normalize [(wire (t, 0), 1)]
  fourth : ∀ t, normalize (ofLC (triple g t 1).c) = normalize [(wire (t, 1), -1)]

structure WriteSeparation {g : Instance} (layout : PowerLayout g) (plan : Plan) : Prop where
  powers : ∀ k, layout.wire k ∉ plan.written
  inputs : ∀ j term, term ∈ g.inputForms j →
    term.1 ∉ plan.written ∧ ∀ k, layout.wire k ≠ term.1

theorem eval_agrees (form : Form) (a b : Assignment)
    (h : ∀ term ∈ form, a term.1 = b term.1) : eval form a = eval form b := by
  unfold eval
  congr 1
  exact List.map_congr_left fun term ht => congrArg (term.2 * ·) (h term ht)

namespace PowerLayout

/-- Each pair `(t,0)` and `(t,1)` receives the square and fourth power. -/
noncomputable def apply {g : Instance} (layout : PowerLayout g) (ambient : Assignment)
    (input : Fin g.tripleCount → F) : Assignment :=
  Function.extend layout.wire (fun k => (input k.1)^(if k.2 = 0 then 2 else 4)) ambient

theorem at_wire {g : Instance} (layout : PowerLayout g) (ambient : Assignment)
    (input : Fin g.tripleCount → F) (k : Fin g.tripleCount × Fin 2) :
    layout.apply ambient input (layout.wire k) =
      (input k.1)^(if k.2 = 0 then 2 else 4) :=
  layout.injective.extend_apply _ ambient k

theorem preserves {g : Instance} (layout : PowerLayout g) (ambient : Assignment)
    (input : Fin g.tripleCount → F) (wire : ℕ) (h : ∀ k, layout.wire k ≠ wire) :
    layout.apply ambient input wire = ambient wire := by
  apply Function.extend_apply'
  simpa only [not_exists] using h

theorem zero {g : Instance} (layout : PowerLayout g) (ambient : Assignment)
    (input : Fin g.tripleCount → F) : layout.apply ambient input 0 = ambient 0 :=
  layout.preserves ambient input 0 layout.nonzero

end PowerLayout

variable {g : Instance} {s : Scheme g.arity g.partialRounds}
  {inputs : Fin g.arity → F}

noncomputable def assign (layout : PowerLayout g) (plan : Plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment) : Assignment :=
  plan.apply (layout.apply ambient (stageInput stages trace)) (desired stages trace)

theorem assign_zero (layout : PowerLayout g) (plan : Plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment) :
    assign layout plan stages trace ambient 0 = ambient 0 := by
  unfold assign
  rw [Plan.zero, PowerLayout.zero]

theorem assign_preserves (layout : PowerLayout g) (plan : Plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment) (wire : ℕ)
    (hrecovery : wire ∉ plan.written) (hpowers : ∀ k, layout.wire k ≠ wire) :
    assign layout plan stages trace ambient wire = ambient wire := by
  unfold assign
  rw [plan.preserves _ _ wire hrecovery, layout.preserves _ _ wire hpowers]

theorem assign_inputs (layout : PowerLayout g) (plan : Plan)
    (separate : WriteSeparation layout plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment) (j : Fin g.arity) :
    eval (g.inputForms j) (assign layout plan stages trace ambient) =
      eval (g.inputForms j) ambient := by
  apply eval_agrees
  intro term ht
  exact assign_preserves layout plan stages trace ambient term.1
    (separate.inputs j term ht).1 (separate.inputs j term ht).2

theorem assign_power (layout : PowerLayout g) (plan : Plan)
    (separate : WriteSeparation layout plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment)
    (k : Fin g.tripleCount × Fin 2) :
    assign layout plan stages trace ambient (layout.wire k) =
      (stageInput stages trace k.1)^(if k.2 = 0 then 2 else 4) := by
  unfold assign
  rw [plan.preserves _ _ _ (separate.powers k), layout.at_wire]

theorem assign_square (layout : PowerLayout g) (plan : Plan)
    (separate : WriteSeparation layout plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment)
    (t : Fin g.tripleCount) :
    (triple g t 1).b.eval (assign layout plan stages trace ambient) =
      (stageInput stages trace t)^2 := by
  have e := eval_certificate _ _ (layout.square t) (assign layout plan stages trace ambient)
  rw [eval_ofLC] at e
  simpa only [eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero, assign_power layout plan separate, ↓reduceIte] using e

theorem assign_fourth (layout : PowerLayout g) (plan : Plan)
    (separate : WriteSeparation layout plan)
    (stages : StageMap g) (trace : Trace s inputs) (ambient : Assignment)
    (t : Fin g.tripleCount) :
    (triple g t 1).c.eval (assign layout plan stages trace ambient) =
      -(stageInput stages trace t)^4 := by
  have e := eval_certificate _ _ (layout.fourth t) (assign layout plan stages trace ambient)
  rw [eval_ofLC] at e
  simpa only [eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    neg_one_mul, add_zero, assign_power layout plan separate,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using e

/-- The nonlinear constraints follow from the constructed powers and the
affine input/output values; this lemma assumes no constraint satisfaction. -/
theorem triple_holds (t : Fin g.tripleCount) (signs : TripleSigns g t)
    (w : Assignment) (x : F)
    (hinput : eval (input g t) w = x)
    (hsquare : (triple g t 1).b.eval w = x^2)
    (hfourth : (triple g t 1).c.eval w = -x^4)
    (houtput : eval (output g t) w = x^5) (j : Fin 3) :
    (triple g t j).Holds w := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := signs
  have e0 := eval_certificate _ _ s0 w
  have e1 := eval_certificate _ _ s1 w
  have e2 := eval_certificate _ _ s2 w
  have e3 := eval_certificate _ _ s3 w
  have e4 := eval_certificate _ _ s4 w
  simp only [eval_ofLC, eval_scale, neg_one_mul, hinput, hsquare, hfourth] at e0 e1 e2 e3 e4
  have h0b : (triple g t 0).b.eval w = x := by
    simpa only [input, eval_ofLC] using hinput
  have h2c : (triple g t 2).c.eval w = -x^5 := by
    simpa only [output, eval_scale, neg_one_mul, eval_ofLC, neg_eq_iff_eq_neg] using houtput
  fin_cases j
  · change (triple g t 0).Holds w
    unfold Constraint.Holds
    rw [e0, h0b, e1]
    ring
  · change (triple g t 1).Holds w
    unfold Constraint.Holds
    rw [e2, hsquare, hfourth]
    ring
  · change (triple g t 2).Holds w
    unfold Constraint.Holds
    rw [e3, e4, h2c]
    ring

end MSP.Artifacts.HashAssignmentCompleteness
