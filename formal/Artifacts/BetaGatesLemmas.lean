import Artifacts.R1CS
import Poseidon.Optimized
import Mathlib.Tactic

/-! Checked sparse affine certificates for the actual beta constraints.
The normalizer is only a certificate checker: its interpretation is proved here.
-/

namespace MSP.Artifacts.BetaGates

abbrev Form := List (ℕ × F)

def eval (a : Form) (w : Assignment) : F := (a.map fun t => t.2 * w t.1).sum
def ofLC (a : LinearCombination) : Form := a.map fun t => (t.1, (t.2 : F))
def scale (c : F) (a : Form) : Form := a.map fun t => (t.1, c * t.2)
def constant (c : F) : Form := [(0, c)]

def insert (i : ℕ) (c : F) : Form → Form
  | [] => if c = 0 then [] else [(i, c)]
  | (j, d) :: xs =>
    if c = 0 then (j, d) :: xs
    else if i < j then (i, c) :: (j, d) :: xs
    else if i = j then
      if c + d = 0 then xs else (j, c + d) :: xs
    else (j, d) :: insert i c xs

def normalize : Form → Form
  | [] => []
  | (i, c) :: xs => insert i c (normalize xs)

theorem eval_insert (i : ℕ) (c : F) (a : Form) (w : Assignment) :
    eval (insert i c a) w = c * w i + eval a w := by
  induction a with
  | nil => by_cases hc : c = 0 <;> simp [insert, eval, hc]
  | cons a xs ih =>
    rcases a with ⟨j, d⟩
    by_cases hc : c = 0
    · simp [insert, eval, hc]
    by_cases hij : i < j
    · simp [insert, eval, hc, hij]
    by_cases heq : i = j
    · subst j
      by_cases hsum : c + d = 0
      · simp only [insert, hc, hij, ↓reduceIte, hsum, eval, List.map_cons, List.sum_cons]
        have hc' : c = -d := eq_neg_of_add_eq_zero_left hsum
        simp [hc']
      · simp [insert, eval, hc, hsum, add_mul, add_assoc]
    · simp only [insert, hc, hij, heq, ↓reduceIte, eval, List.map_cons, List.sum_cons] at *
      rw [ih]
      ring

theorem eval_normalize (a : Form) (w : Assignment) : eval (normalize a) w = eval a w := by
  induction a with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨i, c⟩
    rw [normalize, eval_insert, ih]
    rfl

theorem eval_certificate (a b : Form) (certificate : normalize a = normalize b)
    (w : Assignment) : eval a w = eval b w := by
  rw [← eval_normalize a, certificate, eval_normalize]

@[simp] theorem eval_ofLC (a : LinearCombination) (w : Assignment) :
    eval (ofLC a) w = a.eval w := by
  simp [eval, ofLC, LinearCombination.eval, List.map_map, Function.comp_def]

@[simp] theorem eval_scale (c : F) (a : Form) (w : Assignment) :
    eval (scale c a) w = c * eval a w := by
  simp [scale, eval, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]

@[simp] theorem eval_append (a b : Form) (w : Assignment) :
    eval (a ++ b) w = eval a w + eval b w := by simp [eval]

@[simp] theorem eval_constant (c : F) (w : Assignment) (h : w 0 = 1) :
    eval (constant c) w = c := by simp [constant, eval, h]

def mixForms (m : MSP.Poseidon.Optimized.Matrix11) (s : Fin 11 → Form) : Fin 11 → Form :=
  fun i => ((List.finRange 11).map fun j => scale (m j i) (s j)).flatten

theorem eval_mixForms (m : MSP.Poseidon.Optimized.Matrix11) (s : Fin 11 → Form)
    (w : Assignment) :
    (fun i => eval (mixForms m s i) w) =
      MSP.Poseidon.Optimized.mix m (fun i => eval (s i) w) := by
  funext i
  simp only [mixForms, eval, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]
  change ((List.finRange 11).map fun j => eval (scale (m j i) (s j)) w).sum = _
  simp only [eval_scale, ← List.ofFn_eq_map, List.sum_ofFn]
  simp [MSP.Poseidon.Optimized.mix, Matrix.vecMul, dotProduct, mul_comm, eval]

def evalState (s : Fin 11 → Form) (w : Assignment) : MSP.Poseidon.Optimized.State :=
  fun i => eval (s i) w

def withConstants (s : Fin 11 → Form) (c : MSP.Poseidon.Optimized.State) : Fin 11 → Form :=
  fun i => s i ++ constant (c i)

def replaceFirst (s : Fin 11 → Form) (out : Form) : Fin 11 → Form :=
  fun i => if i = 0 then out else s i

theorem eval_withConstants (s : Fin 11 → Form) (c : MSP.Poseidon.Optimized.State)
    (w : Assignment) (h : w 0 = 1) :
    evalState (withConstants s c) w = evalState s w + c := by
  funext i
  simp [evalState, withConstants, h]

theorem eval_replaceFirst (s : Fin 11 → Form) (out : Form) (w : Assignment) :
    evalState (replaceFirst s out) w = fun i => if i = 0 then eval out w else evalState s w i := by
  funext i
  by_cases hi : i = 0 <;> simp [evalState, replaceFirst, hi]

theorem state_certificate (a b : Fin 11 → Form)
    (certificate : ∀ i, normalize (a i) = normalize (b i)) (w : Assignment) :
    evalState a w = evalState b w := by
  funext i
  exact eval_certificate _ _ (certificate i) w

/-- A finite sequence whose successive states follow the given steps equals their fold. -/
theorem state_fold {α : Type*} (n : ℕ) (s : Fin (n + 1) → α) (step : Fin n → α → α)
    (h : ∀ i, s i.succ = step i (s i.castSucc)) :
    (List.finRange n).foldl (fun a i => step i a) (s 0) = s (Fin.last n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil]
    have hh : ∀ i : Fin n, s i.succ.castSucc = step i.castSucc (s i.castSucc.castSucc) := by
      intro i
      exact h i.castSucc
    have hi := ih (fun i => s i.castSucc) (fun i => step i.castSucc) hh
    simp only [Fin.castSucc_zero] at hi
    rw [hi]
    exact (h (Fin.last n)).symm

/-- Three actual R1CS equations implement x ↦ x⁵, including the optimizer's signs. -/
theorem sigma_equations (x sq quad out : F)
    (h0 : (-x) * x = -sq) (h1 : (-sq) * sq = -quad)
    (h2 : (-quad) * x = -out) : out = x^5 := by
  have hs : sq = x^2 := by linear_combination h0
  have hq : quad = sq^2 := by linear_combination h1
  rw [hs] at hq
  rw [hq] at h2
  linear_combination h2

end MSP.Artifacts.BetaGates
