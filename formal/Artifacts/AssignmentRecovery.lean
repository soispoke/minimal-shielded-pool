import Artifacts.BetaGatesLemmas

/-! Sparse affine recovery for retained circuit wires. A recovery plan supplies
forms over an independent target vector; finite normalized substitution
certificates prove that the recovered assignment realizes those targets.
No circuit-satisfaction or hash-semantics premise is used here. -/

namespace MSP.Artifacts.AssignmentRecovery

open BetaGates

/-- Simultaneous affine substitution, retaining all coefficients for checking. -/
def substitute (form : Form) (replacement : ℕ → Form) : Form :=
  form.flatMap fun term => scale term.2 (replacement term.1)

theorem eval_substitute (form : Form) (replacement : ℕ → Form) (values : Assignment) :
    eval (substitute form replacement) values =
      eval form (fun wire => eval (replacement wire) values) := by
  induction form with
  | nil => simp [substitute, eval]
  | cons term rest ih =>
    simp only [substitute, List.flatMap_cons, eval_append, eval_scale] at *
    rw [ih]
    rfl

/-- Entries declare exactly the wires a plan may overwrite. The target vector
has `count` entries, represented in forms by indices 1 through `count`.
Index zero denotes the ambient constant wire; larger indices encode ambient
wires, so the assignment remains total and preserves wires outside the plan. -/
structure Plan where
  count : ℕ
  entries : List (ℕ × Form)

def lookup : List (ℕ × Form) → ℕ → Option Form
  | [], _ => none
  | (wire, form) :: rest, i => if i = wire then some form else lookup rest i

namespace Plan

def written (plan : Plan) : List ℕ := plan.entries.map Prod.fst

def values (plan : Plan) (ambient : Assignment) (desired : ℕ → F) (i : ℕ) : F :=
  if i = 0 then ambient 0
  else if i ≤ plan.count then desired (i - 1)
  else ambient (i - plan.count - 1)

/-- Wire zero is preserved even if accidentally listed as an entry. -/
def replacement (plan : Plan) (wire : ℕ) : Form :=
  if wire = 0 then [(0, 1)]
  else match lookup plan.entries wire with
    | some form => form
    | none => [(plan.count + 1 + wire, 1)]

def apply (plan : Plan) (ambient : Assignment) (desired : ℕ → F) : Assignment :=
  fun wire => eval (plan.replacement wire) (plan.values ambient desired)

theorem values_target (plan : Plan) (ambient : Assignment) (desired : ℕ → F)
    (i : ℕ) (hi : i < plan.count) :
    plan.values ambient desired (i + 1) = desired i := by
  simp [values, show i + 1 ≤ plan.count by omega]

theorem values_ambient (plan : Plan) (ambient : Assignment) (desired : ℕ → F)
    (wire : ℕ) : plan.values ambient desired (plan.count + 1 + wire) = ambient wire := by
  simp only [values, ite_eq_right (by omega : plan.count + 1 + wire ≠ 0),
    ite_eq_right (by omega : ¬plan.count + 1 + wire ≤ plan.count)]
  congr 1
  omega

theorem zero (plan : Plan) (ambient : Assignment) (desired : ℕ → F) :
    plan.apply ambient desired 0 = ambient 0 := by
  simp [apply, replacement, eval, values]

private theorem lookup_none (entries : List (ℕ × Form)) (wire : ℕ)
    (h : wire ∉ entries.map Prod.fst) : lookup entries wire = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [lookup, ite_eq_right h.1]
    exact ih h.2

/-- Recovery never changes a wire outside its explicit write set. -/
theorem preserves (plan : Plan) (ambient : Assignment) (desired : ℕ → F)
    (wire : ℕ) (h : wire ∉ plan.written) :
    plan.apply ambient desired wire = ambient wire := by
  by_cases hz : wire = 0
  · subst wire
    exact zero plan ambient desired
  · have hl := lookup_none plan.entries wire h
    simp only [apply, replacement, ite_eq_right hz, hl, eval, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, one_mul, add_zero]
    exact values_ambient plan ambient desired wire

/-- A normalized symbolic certificate suffices for arbitrary target values and
arbitrary ambient wires. This is an existence construction, not soundness. -/
theorem realizes (plan : Plan) (form : Form) (target : ℕ)
    (htarget : target < plan.count)
    (certificate : normalize (substitute form plan.replacement) =
      normalize [(target + 1, 1)])
    (ambient : Assignment) (desired : ℕ → F) :
    eval form (plan.apply ambient desired) = desired target := by
  unfold apply
  rw [← eval_substitute]
  rw [eval_certificate _ _ certificate]
  simpa only [eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero] using values_target plan ambient desired target htarget

end Plan
end MSP.Artifacts.AssignmentRecovery
