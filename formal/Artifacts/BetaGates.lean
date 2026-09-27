import Artifacts.BetaGatesSigma
import Artifacts.BetaGatesPartialCertificates
import Artifacts.Compression

/-!
# The pinned beta constraints implement optimized Poseidon

All 153 actual S-box triples and every intervening affine stage are checked.
This proves the beta wire's value on the compression statement projection for
every full satisfying assignment. Ordinary-reference equivalence is separate.
-/

namespace MSP.Artifacts.BetaGates

open BetaGatesData MSP.Poseidon

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

attribute [local irreducible] fullInput fullOutput partialInput

private theorem eval_mix_state (m : Optimized.Matrix11) (s : Fin 11 → Form) (w : Assignment) :
    evalState (mixForms m s) w = Optimized.mix m (evalState s w) := eval_mixForms m s w

private theorem full_sbox (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin 8) :
    evalState (fullOutput r) w = Optimized.sbox (evalState (fullInput r) w) := by
  funext i
  have hi := eval_certificate _ _ (BetaGatesCertificates.full_inputs r i) w
  have ho := eval_certificate _ _ (BetaGatesCertificates.full_outputs r i) w
  change eval (fullOutput r i) w = (eval (fullInput r i) w)^5
  rw [hi, ho]
  by_cases hz : r.val = 0 ∧ i.val = 0
  · simp only [ite_eq_left hz, eval_constant _ _ h.1]
  · simp only [ite_eq_right hz]
    exact sigma_triple w h _

private theorem statement_forms (w : Assignment) :
    (fun i => eval (BetaGatesCertificates.statementForms i) w) = (Compression.statement w).vec := by
  funext i
  fin_cases i <;>
    simp [BetaGatesCertificates.statementForms, eval, Compression.statement, Statement.vec]
  ring

private theorem initial_state (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (fullInput 0) w = Optimized.initialState (Compression.statement w).vec := by
  rw [state_certificate _ _ BetaGatesCertificates.initial w]
  funext i
  simp only [evalState, BetaGatesCertificates.initialForms, eval_append,
    eval_constant _ _ h.1, Optimized.initialState]
  by_cases hi : i.val = 0
  · simp [hi, eval]
  · simp only [dite_eq_right hi]
    rw [congrFun (statement_forms w) ⟨i.val - 1, by omega⟩]

private theorem prefix_step (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin 3) :
    evalState (fullInput ⟨r.val + 1, by omega⟩) w =
      Optimized.prefixStep r.castSucc (evalState (fullInput ⟨r.val, by omega⟩) w) := by
  have e := state_certificate _ _ (BetaGatesCertificates.prefix_steps r) w
  change _ = evalState (mixForms _ _) w at e
  rw [eval_mix_state] at e
  rw [eval_withConstants _ _ _ h.1, full_sbox w h] at e
  simpa only [Optimized.prefixStep, Fin.val_castSucc, ite_eq_right (by omega : r.val ≠ 3)] using e

private theorem prefix_end (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (partialInput 0) w =
      Optimized.prefixStep 3 (evalState (fullInput 3) w) := by
  have e := state_certificate _ _ BetaGatesCertificates.prefix_boundary w
  change _ = evalState (mixForms _ _) w at e
  rw [eval_mix_state] at e
  rw [eval_withConstants _ _ _ h.1, full_sbox w h] at e
  simpa [Optimized.prefixStep] using e

private theorem prefix_state (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (partialInput 0) w = Optimized.prefixState (Compression.statement w).vec := by
  have h0 := prefix_step w h 0
  have h1 := prefix_step w h 1
  have h2 := prefix_step w h 2
  have h3 := prefix_end w h
  change evalState (fullInput 1) w = Optimized.prefixStep 0 (evalState (fullInput 0) w) at h0
  change evalState (fullInput 2) w = Optimized.prefixStep 1 (evalState (fullInput 1) w) at h1
  change evalState (fullInput 3) w = Optimized.prefixStep 2 (evalState (fullInput 2) w) at h2
  change _ = Optimized.prefixStep 3 (Optimized.prefixStep 2
    (Optimized.prefixStep 1 (Optimized.prefixStep 0
      (Optimized.initialState (Compression.statement w).vec))))
  rw [← initial_state w h, ← h0, ← h1, ← h2]
  exact h3

private theorem partial_step (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin 66) :
    evalState (partialInput r.succ) w =
      Optimized.partialStep r (evalState (partialInput r.castSucc) w) := by
  have hi := eval_certificate _ _ (BetaGatesCertificates.partial_inputs r) w
  have hs : eval (output ⟨87 + r.val, by omega⟩) w =
      (evalState (partialInput r.castSucc) w 0)^5 := by
    rw [show evalState (partialInput r.castSucc) w 0 = _ from hi]
    exact sigma_triple w h _
  have hr : evalState (replaceFirst (partialInput r.castSucc) (output ⟨87 + r.val, by omega⟩)) w =
      Optimized.partialSbox (evalState (partialInput r.castSucc) w) := by
    rw [eval_replaceFirst]
    funext i
    by_cases hz : i = 0
    · subst i
      simp [Optimized.partialSbox, hs]
    · simp [Optimized.partialSbox, hz]
  have e := state_certificate _ _ (BetaGatesCertificates.partial_steps r) w
  change _ = evalState (mixForms _ _) w at e
  rw [eval_mix_state] at e
  rw [eval_withConstants _ _ _ h.1, hr] at e
  exact e

private theorem partial_state (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (partialInput 66) w = Optimized.partialState (Compression.statement w).vec := by
  unfold Optimized.partialState
  rw [← prefix_state w h]
  exact (state_fold 66 (fun r => evalState (partialInput r) w)
    Optimized.partialStep (partial_step w h)).symm

private theorem suffix_start (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (fullInput 4) w = Optimized.partialState (Compression.statement w).vec :=
  (state_certificate _ _ BetaGatesCertificates.partial_boundary w).trans (partial_state w h)

private theorem suffix_step (w : Assignment) (h : Spend.system.Satisfied w) (r : Fin 3) :
    evalState (fullInput ⟨r.val + 5, by omega⟩) w =
      Optimized.suffixStep r (evalState (fullInput ⟨r.val + 4, by omega⟩) w) := by
  have e := state_certificate _ _ (BetaGatesCertificates.suffix r) w
  change _ = evalState (mixForms _ _) w at e
  rw [eval_mix_state] at e
  rw [eval_withConstants _ _ _ h.1, full_sbox w h] at e
  exact e

private theorem suffix_state (w : Assignment) (h : Spend.system.Satisfied w) :
    evalState (fullInput 7) w = Optimized.suffixState (Compression.statement w).vec := by
  unfold Optimized.suffixState
  rw [← suffix_start w h]
  exact (state_fold 3 (fun r => evalState (fullInput ⟨r.val + 4, by omega⟩) w)
    Optimized.suffixStep (suffix_step w h)).symm

/-- The actual beta output equals optimized Poseidon of all ten projected statement fields. -/
theorem beta_of_system (w : Assignment) (h : Spend.system.Satisfied w) :
    w 1 = Optimized.hash10 (Compression.statement w).vec := by
  have e := eval_certificate _ _ BetaGatesCertificates.final_mix w
  simp only [eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero] at e
  change w 1 = evalState (mixForms Optimized.M (fullOutput 7)) w 0 at e
  rw [eval_mix_state] at e
  rw [full_sbox w h, suffix_state w h] at e
  exact e

#print axioms beta_of_system

end MSP.Artifacts.BetaGates
