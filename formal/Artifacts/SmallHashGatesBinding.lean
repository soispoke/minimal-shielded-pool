import Artifacts.SmallHashGatesSchedule

/-! Compose actual S-box semantics with all affine certificates into the whole
optimized hash. Every certificate premise is later discharged for each instance.
-/

namespace MSP.Artifacts.SmallHashGates

open BetaGates MSP.Poseidon

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def inputValues (g : Instance) (w : Assignment) : Fin g.arity → F :=
  fun j => eval (g.inputForms j) w

private theorem full_sbox (g : Instance) (s : Scheme g.arity g.partialRounds)
    (signs : ∀ t, TripleSigns g t) (w : Assignment) (h : Spend.system.Satisfied w)
    (r : Fin 8) (j : Fin (g.arity + 1)) :
    eval (fullOutputForm g s.initialConstants r j) w =
      (eval (fullInputForm g s.initialConstants r j) w)^5 := by
  cases hs : g.fullStage r j with
  | none => simpa only [fullInputForm, fullOutputForm, hs] using
      folded_sbox ((g.foldedInput j).getD 0 + s.initialConstants j) w h.1
  | some t => simpa only [fullInputForm, fullOutputForm, hs] using sigma_of_signs g t (signs t) w h

private theorem initial_state (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (fullInputForm g s.initialConstants 0) w = s.initialState (inputValues g w) := by
  rw [state_certificate _ _ c.initial w]
  funext j
  simp only [evalState, initialForms, eval_append, eval_constant _ _ h.1, Scheme.initialState]
  by_cases hj : j.val = 0
  · simp [hj, eval]
  · simp only [dite_eq_right hj, inputValues]

private theorem prefix_step (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin 3) :
    evalState (fullInputForm g s.initialConstants ⟨r.val + 1, by omega⟩) w =
      s.prefixStep r.castSucc (evalState (fullInputForm g s.initialConstants ⟨r.val, by omega⟩) w) := by
  have e := full_round _ _ _ s.mds (s.prefixConstants r.castSucc) (c.prefixSteps r) w h.1
    (full_sbox g s signs w h ⟨r.val, by omega⟩)
  simpa only [Scheme.prefixStep, Fin.val_castSucc, ite_eq_right (by omega : r.val ≠ 3)] using e

private theorem prefix_end (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (c.partialStates 0) w =
      s.prefixStep 3 (evalState (fullInputForm g s.initialConstants 3) w) := by
  have e := full_round _ _ _ s.preMatrix (s.prefixConstants 3) c.prefixBoundary w h.1
    (full_sbox g s signs w h 3)
  simpa [Scheme.prefixStep] using e

private theorem prefix_state (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (c.partialStates 0) w = s.prefixState (inputValues g w) := by
  have h0 := prefix_step g s c signs w h 0
  have h1 := prefix_step g s c signs w h 1
  have h2 := prefix_step g s c signs w h 2
  have h3 := prefix_end g s c signs w h
  change evalState (fullInputForm g s.initialConstants 1) w =
    s.prefixStep 0 (evalState (fullInputForm g s.initialConstants 0) w) at h0
  change evalState (fullInputForm g s.initialConstants 2) w =
    s.prefixStep 1 (evalState (fullInputForm g s.initialConstants 1) w) at h1
  change evalState (fullInputForm g s.initialConstants 3) w =
    s.prefixStep 2 (evalState (fullInputForm g s.initialConstants 2) w) at h2
  change _ = s.prefixStep 3 (s.prefixStep 2 (s.prefixStep 1
    (s.prefixStep 0 (s.initialState (inputValues g w)))))
  rw [← initial_state g s c w h, ← h0, ← h1, ← h2]
  exact h3

private theorem partial_step (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin g.partialRounds) :
    evalState (c.partialStates r.succ) w = s.partialStep r (evalState (c.partialStates r.castSucc) w) := by
  have hi := eval_certificate _ _ (c.partialInputs r) w
  have hs : eval (partialOutputForm g r) w = (eval (c.partialStates r.castSucc 0) w)^5 := by
    rw [hi]
    exact sigma_of_signs g (g.partialStage r) (signs _) w h
  have e := partial_round _ _ _ (s.sparseMatrices r) (s.partialConstants r) (c.partialSteps r) w h.1 hs
  refine e.trans ?_
  unfold Scheme.partialStep
  congr 1
  funext j
  by_cases hj : j = 0 <;> simp [hj]

private theorem partial_state (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (c.partialStates (Fin.last g.partialRounds)) w = s.partialState (inputValues g w) := by
  unfold Scheme.partialState
  rw [← prefix_state g s c signs w h]
  exact (state_fold g.partialRounds (fun r => evalState (c.partialStates r) w)
    s.partialStep (partial_step g s c signs w h)).symm

private theorem suffix_start (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (fullInputForm g s.initialConstants 4) w = s.partialState (inputValues g w) :=
  (state_certificate _ _ c.partialBoundary w).trans (partial_state g s c signs w h)

private theorem suffix_step (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin 3) :
    evalState (fullInputForm g s.initialConstants ⟨r.val + 5, by omega⟩) w =
      s.suffixStep r (evalState (fullInputForm g s.initialConstants ⟨r.val + 4, by omega⟩) w) := by
  exact full_round _ _ _ s.mds (s.suffixConstants r) (c.suffixSteps r) w h.1
    (full_sbox g s signs w h ⟨r.val + 4, by omega⟩)

private theorem suffix_state (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (fullInputForm g s.initialConstants 7) w = s.suffixState (inputValues g w) := by
  unfold Scheme.suffixState
  rw [← suffix_start g s c signs w h]
  exact (state_fold 3
    (fun r => evalState (fullInputForm g s.initialConstants ⟨r.val + 4, by omega⟩) w)
    s.suffixStep (suffix_step g s c signs w h)).symm

/-- All rounds of a concrete instance, under explicit kernel-checked coefficient
certificates and actual constraint sign certificates. -/
theorem hash_of_affine (g : Instance) (s : Scheme g.arity g.partialRounds)
    (c : AffineCertificates g s) (signs : ∀ t, TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    eval g.outputForm w = s.hash (inputValues g w) := by
  have e := eval_certificate _ _ c.finalMix w
  change _ = evalState (mixForms s.mds (fullOutputForm g s.initialConstants 7)) w 0 at e
  rw [eval_mixForms] at e
  have hs : evalState (fullOutputForm g s.initialConstants 7) w =
      fun j => (evalState (fullInputForm g s.initialConstants 7) w j)^5 :=
    funext (full_sbox g s signs w h 7)
  rw [hs, suffix_state g s c signs w h] at e
  exact e

#print axioms hash_of_affine

end MSP.Artifacts.SmallHashGates
