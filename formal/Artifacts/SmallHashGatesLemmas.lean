import Artifacts.BetaGatesLemmas
import Artifacts.Spend

/-! Reusable actual S-box semantics and width-generic affine round assembly.
These helpers leave all coefficient identities explicit for kernel checking.
-/

namespace MSP.Artifacts.SmallHashGates

open BetaGates

/-- A concrete slice of the full constraint system, with typed source-stage indices.
Interface forms become hash bindings only after all affine certificates are proved. -/
structure Instance where
  name : String
  arity : ℕ
  partialRounds : ℕ
  tripleCount : ℕ
  constraints : List Constraint
  constraintCount : constraints.length = 3 * tripleCount
  contains : ∀ c ∈ constraints, c ∈ Spend.system.constraints
  fullStage : Fin 8 → Fin (arity + 1) → Option (Fin tripleCount)
  partialStage : Fin partialRounds → Fin tripleCount
  foldedInput : Fin (arity + 1) → Option F
  inputForms : Fin arity → Form
  outputForm : Form

def triple (g : Instance) (t : Fin g.tripleCount) (j : Fin 3) : Constraint :=
  g.constraints[3 * t.val + j.val]'(by rw [g.constraintCount]; omega)

def input (g : Instance) (t : Fin g.tripleCount) : Form := ofLC (triple g t 0).b
def output (g : Instance) (t : Fin g.tripleCount) : Form := scale (-1) (ofLC (triple g t 2).c)

def TripleSigns (g : Instance) (t : Fin g.tripleCount) : Prop :=
  normalize (ofLC (triple g t 0).a) = normalize (scale (-1) (input g t)) ∧
  normalize (ofLC (triple g t 0).c) = normalize (scale (-1) (ofLC (triple g t 1).b)) ∧
  normalize (ofLC (triple g t 1).a) = normalize (scale (-1) (ofLC (triple g t 1).b)) ∧
  normalize (ofLC (triple g t 2).a) = normalize (ofLC (triple g t 1).c) ∧
  normalize (ofLC (triple g t 2).b) = normalize (input g t)

theorem triple_mem (g : Instance) (t : Fin g.tripleCount) (j : Fin 3) :
    triple g t j ∈ Spend.system.constraints := g.contains _ (List.getElem_mem _)

theorem sigma_of_signs (g : Instance) (t : Fin g.tripleCount) (signs : TripleSigns g t)
    (w : Assignment) (h : Spend.system.Satisfied w) :
    eval (output g t) w = (eval (input g t) w)^5 := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := signs
  have e0 := eval_certificate _ _ s0 w
  have e1 := eval_certificate _ _ s1 w
  have e2 := eval_certificate _ _ s2 w
  have e3 := eval_certificate _ _ s3 w
  have e4 := eval_certificate _ _ s4 w
  simp only [eval_ofLC, eval_scale, neg_one_mul] at e0 e1 e2 e3 e4
  have h0 := h.2 _ (triple_mem g t 0)
  have h1 := h.2 _ (triple_mem g t 1)
  have h2 := h.2 _ (triple_mem g t 2)
  unfold Constraint.Holds at h0 h1 h2
  rw [e0, e1] at h0
  rw [e2] at h1
  rw [e3, e4] at h2
  simp only [output, eval_scale, eval_ofLC, neg_one_mul]
  apply sigma_equations (eval (input g t) w) ((triple g t 1).b.eval w)
    (-((triple g t 1).c.eval w)) (-((triple g t 2).c.eval w))
  · simpa only [input, eval_ofLC] using h0
  · simpa only [neg_neg] using h1
  · simpa only [neg_neg] using h2

/-- Constant-folded S-box coordinates need no trusted witness-generation claim. -/
theorem folded_sbox (c : F) (w : Assignment) (h : w 0 = 1) :
    eval (constant (c^5)) w = (eval (constant c) w)^5 := by simp [h]

def evalState {n : ℕ} (s : Fin n → Form) (w : Assignment) : Fin n → F :=
  fun i => eval (s i) w

def mixForms {n : ℕ} (m : Matrix (Fin n) (Fin n) F) (s : Fin n → Form) : Fin n → Form :=
  fun i => ((List.finRange n).map fun j => scale (m j i) (s j)).flatten

def withConstants {n : ℕ} (s : Fin n → Form) (c : Fin n → F) : Fin n → Form :=
  fun i => s i ++ constant (c i)

theorem eval_mixForms {n : ℕ} (m : Matrix (Fin n) (Fin n) F) (s : Fin n → Form)
    (w : Assignment) : evalState (mixForms m s) w = Matrix.vecMul (evalState s w) m := by
  funext i
  simp only [evalState, mixForms, eval, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]
  change ((List.finRange n).map fun j => eval (scale (m j i) (s j)) w).sum = _
  simp only [eval_scale, ← List.ofFn_eq_map, List.sum_ofFn]
  simp [Matrix.vecMul, dotProduct, mul_comm, eval, evalState]

theorem eval_withConstants {n : ℕ} (s : Fin n → Form) (c : Fin n → F)
    (w : Assignment) (h : w 0 = 1) :
    evalState (withConstants s c) w = evalState s w + c := by
  funext i
  simp [evalState, withConstants, h]

theorem state_certificate {n : ℕ} (a b : Fin n → Form)
    (certificate : ∀ i, normalize (a i) = normalize (b i)) (w : Assignment) :
    evalState a w = evalState b w := by
  funext i
  exact eval_certificate _ _ (certificate i) w

/-- Assemble a full round from actual S-box equations and checked affine coefficients. -/
theorem full_round {n : ℕ} (before boxes after : Fin n → Form)
    (m : Matrix (Fin n) (Fin n) F) (c : Fin n → F)
    (affine : ∀ i, normalize (after i) = normalize (mixForms m (withConstants boxes c) i))
    (w : Assignment) (hzero : w 0 = 1)
    (hsigma : ∀ i, eval (boxes i) w = (eval (before i) w)^5) :
    evalState after w = Matrix.vecMul ((fun i => (evalState before w i)^5) + c) m := by
  rw [state_certificate _ _ affine, eval_mixForms, eval_withConstants _ _ _ hzero]
  have hs : evalState boxes w = fun i => (evalState before w i)^5 := funext hsigma
  rw [hs]

/-- Assemble a partial round once its sole nonlinear coordinate is bound. -/
theorem partial_round {n : ℕ} (before after : Fin (n + 1) → Form) (box : Form)
    (m : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (c : F)
    (affine : ∀ i, normalize (after i) = normalize
      (mixForms m (fun j => if j = 0 then box ++ constant c else before j) i))
    (w : Assignment) (hzero : w 0 = 1)
    (hsigma : eval box w = (eval (before 0) w)^5) :
    evalState after w = Matrix.vecMul
      (fun i => if i = 0 then (evalState before w i)^5 + c else evalState before w i) m := by
  rw [state_certificate _ _ affine, eval_mixForms]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp [evalState, hzero, hsigma]
  · simp [evalState, hi]

end MSP.Artifacts.SmallHashGates
