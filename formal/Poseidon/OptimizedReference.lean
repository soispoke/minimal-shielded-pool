import Poseidon.OptimizedCertificates
import Poseidon.Hash

/-! Connect the indexed pre-S-box recurrence to the exact ordinary reference
permutation. Optimized schedule equivalence is proved separately. -/

namespace MSP.Poseidon.Optimized

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def run {α : Type} {n : ℕ} (step : Fin n → α → α) (start : α) (k : ℕ) : α :=
  ((List.finRange n).take k).foldl (fun s r => step r s) start

theorem run_zero {α : Type} {n : ℕ} (step : Fin n → α → α) (start : α) :
    run step start 0 = start := rfl

theorem run_succ {α : Type} {n k : ℕ} (step : Fin n → α → α) (start : α)
    (h : k < n) : run step start (k + 1) = step ⟨k, h⟩ (run step start k) := by
  unfold run
  rw [List.take_succ_eq_append_getElem (by simpa using h), List.foldl_append]
  simp

theorem run_full {α : Type} {n : ℕ} (step : Fin n → α → α) (start : α) :
    run step start n = (List.finRange n).foldl (fun s r => step r s) start := by
  unfold run
  rw [List.take_of_length_le (by simp [List.finRange])]

private theorem get_ofFn {n : ℕ} (f : Fin n → F) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]
  congr 1

theorem reference_round (r : Fin 74) (v : Vector F 11) :
    (fun i => (round params11 r v).get i) =
      mix M (fun i => if r.val < 4 ∨ 70 ≤ r.val ∨ i = 0 then
          (v.get i + referenceConstant r i) ^ 5 else v.get i + referenceConstant r i) := by
  funext i
  have hfr : params11.fullRounds = 8 := rfl
  have hpr : params11.partialRounds = 66 := rfl
  simp only [round, get_ofFn, hfr, hpr, Nat.reduceDiv, Nat.reduceAdd, mix, Matrix.vecMul, dotProduct,
    Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]
  congr 1
  funext a j
  rw [matrix_reference, mul_comm]
  congr 2
  simp only [referenceConstant, Fin.ext_iff, Fin.val_zero]

def referenceStart (inputs : Fin 10 → F) : Vector F 11 :=
  Vector.ofFn fun i : Fin 11 =>
    if h : i.val = 0 then 0 else inputs ⟨i.val - 1, by omega⟩

def referenceState (inputs : Fin 10 → F) (k : ℕ) : Vector F 11 :=
  run (fun r : Fin 74 => round params11 r) (referenceStart inputs) k

def referencePre (inputs : Fin 10 → F) (r : Fin 74) : State :=
  fun i => (referenceState inputs r.val).get i + referenceConstant r i

theorem reference_initial (inputs : Fin 10 → F) :
    initialState inputs = referencePre inputs 0 := by
  funext i
  simp only [initialState, referencePre, referenceState, Fin.val_zero, run_zero, referenceStart,
    get_ofFn, initial_constant]

theorem reference_full_next (inputs : Fin 10 → F) (r : Fin 73)
    (h : r.val < 4 ∨ 70 ≤ r.val) :
    referencePre inputs ⟨r.val + 1, by omega⟩ =
      mix M (sbox (referencePre inputs ⟨r.val, by omega⟩)) +
        referenceConstant ⟨r.val + 1, by omega⟩ := by
  unfold referencePre referenceState
  rw [run_succ (fun r : Fin 74 => round params11 r) (referenceStart inputs) (show r.val < 74 by omega)]
  have hr := reference_round ⟨r.val, by omega⟩
    (run (fun r : Fin 74 => round params11 r) (referenceStart inputs) r.val)
  have hall : ∀ i : Fin 11, r.val < 4 ∨ 70 ≤ r.val ∨ i = 0 := by
    intro i
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  simp only [hall, ↓reduceIte] at hr
  funext i
  exact congrArg (· + referenceConstant ⟨r.val + 1, by omega⟩ i) (congrFun hr i)

theorem reference_partial_next (inputs : Fin 10 → F) (r : Fin 73)
    (h : 4 ≤ r.val ∧ r.val < 70) :
    referencePre inputs ⟨r.val + 1, by omega⟩ =
      mix M (partialSbox (referencePre inputs ⟨r.val, by omega⟩)) +
        referenceConstant ⟨r.val + 1, by omega⟩ := by
  unfold referencePre referenceState
  rw [run_succ (fun r : Fin 74 => round params11 r) (referenceStart inputs) (show r.val < 74 by omega)]
  have hr := reference_round ⟨r.val, by omega⟩
    (run (fun r : Fin 74 => round params11 r) (referenceStart inputs) r.val)
  have h0 : ¬ r.val < 4 := by omega
  have h1 : ¬ 70 ≤ r.val := by omega
  simp only [h0, h1, false_or] at hr
  funext i
  exact congrArg (· + referenceConstant ⟨r.val + 1, by omega⟩ i) (congrFun hr i)

theorem reference_hash (inputs : Fin 10 → F) :
    MSP.Poseidon.hash10 inputs = (mix M (sbox (referencePre inputs 73))) 0 := by
  have hr := reference_round 73 (referenceState inputs 73)
  simp only [show ¬ (73 : Fin 74).val < 4 by decide,
    show 70 ≤ (73 : Fin 74).val by decide, or_true, true_or, ↓reduceIte] at hr
  have he : MSP.Poseidon.hash10 inputs = (referenceState inputs 74).get 0 := by
    unfold MSP.Poseidon.hash10 hash referenceState
    rw [run_full (step := fun r : Fin 74 => round params11 r)]
    simp only [get_ofFn]
    rfl
  rw [he]
  unfold referenceState
  rw [run_succ (fun r : Fin 74 => round params11 r) (referenceStart inputs) (by decide : 73 < 74)]
  exact congrFun hr 0

end MSP.Poseidon.Optimized
