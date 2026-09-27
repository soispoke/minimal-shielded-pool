import Artifacts.AssignmentRecovery
import Artifacts.SmallHashGatesData

/-! Transport shared sparse recovery templates to exact physical wire names.
The template and transport equations remain explicit kernel-checked premises. -/

namespace MSP.Artifacts.AssignmentRecoverySmall

open BetaGates AssignmentRecovery

def rename (form : Form) (wireMap : ℕ → ℕ) : Form :=
  form.map fun term => (wireMap term.1, term.2)

theorem eval_rename (form : Form) (wireMap : ℕ → ℕ) (a : Assignment) :
    eval (rename form wireMap) a = eval form (fun j => a (wireMap j)) := by
  simp [rename, eval, List.map_map, Function.comp_def]

private theorem eval_congr (form : Form) (a b : Assignment)
    (h : ∀ term ∈ form, a term.1 = b term.1) : eval form a = eval form b := by
  unfold eval
  congr 1
  apply List.map_congr_left
  intro term hterm
  rw [h term hterm]

/-- Transport a template realization without recomputing its matrix inverse.
The only per-instance facts are a coefficient identity for its output form,
exact replacement forms for supported template wires, and the matching count. -/
theorem realizes_renamed (template actual : Plan) (templateForm actualForm : Form)
    (wireMap : ℕ → ℕ) (target : ℕ) (htarget : target < template.count)
    (count_eq : actual.count = template.count)
    (template_certificate : normalize (substitute templateForm template.replacement) =
      normalize [(target + 1, 1)])
    (form_certificate : normalize actualForm = normalize (rename templateForm wireMap))
    (support : ∀ term ∈ templateForm, term.1 ≤ template.count)
    (replacements : ∀ j ≤ template.count,
      actual.replacement (wireMap j) = template.replacement j)
    (ambient : Assignment) (desired : ℕ → F) :
    eval actualForm (actual.apply ambient desired) = desired target := by
  rw [eval_certificate _ _ form_certificate, eval_rename]
  have eq_values : actual.values ambient desired = template.values ambient desired := by
    funext j
    simp only [Plan.values, count_eq]
  calc
    eval templateForm (fun j => actual.apply ambient desired (wireMap j)) =
        eval templateForm (template.apply ambient desired) := by
      apply eval_congr
      intro term hterm
      simp only [Plan.apply, replacements term.1 (support term hterm), eq_values]
    _ = desired target := template.realizes templateForm target htarget
      template_certificate ambient desired

end MSP.Artifacts.AssignmentRecoverySmall
