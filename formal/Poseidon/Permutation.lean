import Spec.Basic

/-! The ordinary circomlibjs reference permutation, over the BN254 scalar
field. The optimized Circom circuit's equivalence to this function remains a
separate obligation. -/

namespace MSP.Poseidon

/-- Typed parameters: every round has exactly one constant per state element,
and the mixing matrix has exactly the state width in both dimensions. -/
structure Parameters (t : ℕ) where
  fullRounds : ℕ
  partialRounds : ℕ
  constants : Vector (Vector F t) (fullRounds + partialRounds)
  matrix : Vector (Vector F t) t

/-- Add round constants, apply the fifth-power S-box (to every element in full
rounds and only element zero in partial rounds), then multiply by the matrix.
The matrix convention is `new[i] = Σ_j M[i][j] * state[j]`. -/
def round {t : ℕ} (params : Parameters t)
    (r : Fin (params.fullRounds + params.partialRounds)) (state : Vector F t) : Vector F t :=
  let added := Vector.ofFn fun i => state.get i + (params.constants.get r).get i
  let substituted := Vector.ofFn fun i =>
    if r.val < params.fullRounds / 2 ∨
        params.fullRounds / 2 + params.partialRounds ≤ r.val ∨ i.val = 0 then
      (added.get i) ^ 5
    else added.get i
  Vector.ofFn fun i => (List.finRange t).foldl
    (fun acc j => acc + (params.matrix.get i).get j * substituted.get j) 0

/-- Execute the rounds in increasing order. Vectors materialize each state,
so evaluating a later round does not recompute earlier rounds per matrix entry. -/
def permute {t : ℕ} (params : Parameters t) (state : Vector F t) : Vector F t :=
  (List.finRange (params.fullRounds + params.partialRounds)).foldl
    (fun state r => round params r state) state

/-- State starts at `[0, inputs...]`; the hash is the final element zero. -/
def hash {n : ℕ} (params : Parameters (n + 1)) (inputs : Vector F n) : F :=
  let initial := Vector.ofFn fun i : Fin (n + 1) =>
    if h : i.val = 0 then 0 else inputs.get ⟨i.val - 1, by omega⟩
  (permute params initial).get ⟨0, Nat.succ_pos _⟩

end MSP.Poseidon
