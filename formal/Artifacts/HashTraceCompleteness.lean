import Artifacts.SmallHashGatesSchedule
import Poseidon.OptimizedReference

/-! Construct every optimized hash state from arbitrary inputs.  This is the
semantic trace used to reconstruct the physical R1CS assignment in completeness:
none of its equations assumes R1CS satisfaction or a supplied hash output. -/

namespace MSP.Artifacts.HashTraceCompleteness

open SmallHashGates MSP.Poseidon.Optimized

set_option maxHeartbeats 1000000

abbrev State (arity : ℕ) := Fin (arity + 1) → F

/-- The eight full S-box layers and the intervening partial layers, including
their affine transitions.  Indices agree with `SmallHashGates.Instance`'s
`fullStage` and `partialStage` maps. -/
structure Trace {arity rp : ℕ} (s : Scheme arity rp) (inputs : Fin arity → F) where
  fullInput : Fin 8 → State arity
  fullOutput : Fin 8 → State arity
  partialState : Fin (rp + 1) → State arity
  partialOutput : Fin rp → F
  output : F
  initial : fullInput 0 = s.initialState inputs
  fullSbox : ∀ r j, fullOutput r j = (fullInput r j)^5
  prefixSteps : ∀ r : Fin 3,
    fullInput ⟨r.val + 1, by omega⟩ =
      Matrix.vecMul (fullOutput ⟨r.val, by omega⟩ + s.prefixConstants r.castSucc) s.mds
  prefixBoundary : partialState 0 =
    Matrix.vecMul (fullOutput 3 + s.prefixConstants 3) s.preMatrix
  partialSbox : ∀ r, partialOutput r = (partialState r.castSucc 0)^5
  partialSteps : ∀ r,
    partialState r.succ = Matrix.vecMul
      (fun j => if j = 0 then partialOutput r + s.partialConstants r
        else partialState r.castSucc j) (s.sparseMatrices r)
  partialBoundary : fullInput 4 = partialState (Fin.last rp)
  suffixSteps : ∀ r : Fin 3,
    fullInput ⟨r.val + 5, by omega⟩ =
      Matrix.vecMul (fullOutput ⟨r.val + 4, by omega⟩ + s.suffixConstants r) s.mds
  finalMix : output = (Matrix.vecMul (fullOutput 7) s.mds) 0
  output_hash : output = s.hash inputs

variable {arity rp : ℕ} (s : Scheme arity rp) (inputs : Fin arity → F)

/-- Canonical input to each full S-box layer. -/
def fullInputAt (r : Fin 8) : State arity :=
  if r.val < 4 then run s.prefixStep (s.initialState inputs) r.val
  else run s.suffixStep (s.partialState inputs) (r.val - 4)

/-- Canonical state before each partial layer, together with the final state. -/
def partialStateAt (r : Fin (rp + 1)) : State arity :=
  run s.partialStep (s.prefixState inputs) r.val

theorem fullInputAt_prefix (r : Fin 4) :
    fullInputAt s inputs ⟨r.val, by omega⟩ =
      run s.prefixStep (s.initialState inputs) r.val := by
  simp only [fullInputAt, r.isLt, ↓reduceIte]

theorem fullInputAt_suffix (r : Fin 4) :
    fullInputAt s inputs ⟨r.val + 4, by omega⟩ =
      run s.suffixStep (s.partialState inputs) r.val := by
  simp only [fullInputAt, show ¬ r.val + 4 < 4 by omega, ↓reduceIte,
    Nat.add_sub_cancel]

theorem fullInputAt_initial : fullInputAt s inputs 0 = s.initialState inputs := by
  exact fullInputAt_prefix s inputs 0

theorem fullInputAt_prefix_step (r : Fin 3) :
    fullInputAt s inputs ⟨r.val + 1, by omega⟩ =
      Matrix.vecMul ((fun j => (fullInputAt s inputs ⟨r.val, by omega⟩ j)^5) +
        s.prefixConstants r.castSucc) s.mds := by
  simp only [fullInputAt, show r.val + 1 < 4 by omega, show r.val < 4 by omega,
    ↓reduceIte]
  rw [run_succ s.prefixStep (s.initialState inputs) (show r.val < 4 by omega)]
  simp only [Scheme.prefixStep, show ¬ r.val = 3 by omega, ↓reduceIte]
  rw [show (⟨r.val, by omega⟩ : Fin 4) = r.castSucc by
    apply Fin.ext; simp only [Fin.val_castSucc]]

theorem partialStateAt_initial : partialStateAt s inputs 0 = s.prefixState inputs := by
  simp only [partialStateAt, Fin.val_zero, run_zero]

theorem partialStateAt_prefix_boundary :
    partialStateAt s inputs 0 =
      Matrix.vecMul ((fun j => (fullInputAt s inputs 3 j)^5) + s.prefixConstants 3)
        s.preMatrix := by
  rw [partialStateAt_initial]
  simp only [fullInputAt]
  unfold Scheme.prefixState
  rw [← run_full s.prefixStep (s.initialState inputs)]
  rw [run_succ s.prefixStep (s.initialState inputs) (show 3 < 4 by decide)]
  rfl

theorem partialStateAt_step (r : Fin rp) :
    partialStateAt s inputs r.succ = Matrix.vecMul
      (fun j => if j = 0 then (partialStateAt s inputs r.castSucc 0)^5 + s.partialConstants r
        else partialStateAt s inputs r.castSucc j) (s.sparseMatrices r) := by
  simp only [partialStateAt, Fin.val_succ, Fin.val_castSucc]
  rw [run_succ s.partialStep (s.prefixState inputs) r.isLt]
  unfold Scheme.partialStep
  congr 1
  funext j
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj]

theorem partialStateAt_final :
    partialStateAt s inputs (Fin.last rp) = s.partialState inputs := by
  simpa only [partialStateAt, Fin.val_last, Scheme.partialState] using
    run_full s.partialStep (s.prefixState inputs)

theorem fullInputAt_partial_boundary :
    fullInputAt s inputs 4 = partialStateAt s inputs (Fin.last rp) := by
  rw [partialStateAt_final]
  exact fullInputAt_suffix s inputs 0

theorem fullInputAt_suffix_step (r : Fin 3) :
    fullInputAt s inputs ⟨r.val + 5, by omega⟩ =
      Matrix.vecMul ((fun j => (fullInputAt s inputs ⟨r.val + 4, by omega⟩ j)^5) +
        s.suffixConstants r) s.mds := by
  simp only [fullInputAt, show ¬ r.val + 5 < 4 by omega,
    show ¬ r.val + 4 < 4 by omega, ↓reduceIte, Nat.add_sub_cancel,
    show r.val + 5 - 4 = r.val + 1 by omega]
  rw [run_succ s.suffixStep (s.partialState inputs) r.isLt]
  rfl

theorem fullInputAt_final : fullInputAt s inputs 7 = s.suffixState inputs := by
  have h := fullInputAt_suffix s inputs ⟨3, by omega⟩
  change fullInputAt s inputs 7 = run s.suffixStep (s.partialState inputs) 3 at h
  rw [h]
  exact run_full s.suffixStep (s.partialState inputs)

/-- An explicit trace for every input vector, without any satisfaction premise. -/
def construct : Trace s inputs where
  fullInput := fullInputAt s inputs
  fullOutput := fun r j => (fullInputAt s inputs r j)^5
  partialState := partialStateAt s inputs
  partialOutput := fun r => (partialStateAt s inputs r.castSucc 0)^5
  output := (Matrix.vecMul (fun j => (fullInputAt s inputs 7 j)^5) s.mds) 0
  initial := fullInputAt_initial s inputs
  fullSbox := fun _ _ => rfl
  prefixSteps := fullInputAt_prefix_step s inputs
  prefixBoundary := partialStateAt_prefix_boundary s inputs
  partialSbox := fun _ => rfl
  partialSteps := partialStateAt_step s inputs
  partialBoundary := fullInputAt_partial_boundary s inputs
  suffixSteps := fullInputAt_suffix_step s inputs
  finalMix := rfl
  output_hash := by rw [fullInputAt_final]; rfl

end MSP.Artifacts.HashTraceCompleteness
