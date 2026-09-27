import Artifacts.SemanticAssignmentHashes
import Artifacts.HashAssignmentCompletenessSmall
import Artifacts.CircuitAssemblyLayoutBindings
import Artifacts.CircuitAssemblyLayoutExclusive

/-! Compatibility of the independent hash witnesses with the shared semantic
assignment. Equal extracted input forms and two proved reference interfaces
force equal outputs; no full-circuit satisfaction is used. -/

namespace MSP.Artifacts.SemanticAssignment

open BetaGates SmallHashGates SmallHashGatesData

private theorem small_arity (i : Fin 54) : (gate i).arity = 2 ∨ (gate i).arity = 3 := by
  fin_cases i <;> decide

theorem output_eq_of_bindings (i : Fin 54) (a b : Assignment)
    (ha : HashBinding a i) (hb : HashBinding b i)
    (hi : ∀ j, eval ((gate i).inputForms j) a = eval ((gate i).inputForms j) b) :
    eval (gate i).outputForm a = eval (gate i).outputForm b := by
  have hin (j : ℕ) : eval (inputAt (gate i) j) a = eval (inputAt (gate i) j) b := by
    unfold inputAt
    split
    · exact hi _
    · rfl
  rcases small_arity i with h2 | h3
  · simp only [HashBinding, h2] at ha hb
    rw [hin 0, hin 1] at ha
    exact ha.trans hb.symm
  · simp only [HashBinding, h3] at ha hb
    rw [hin 0, hin 1, hin 2] at ha
    exact ha.trans hb.symm

theorem small_output_eq (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w)
    (i : Fin 54) :
    eval (gate i).outputForm (HashAssignmentCompletenessSmall.assignment i (build x w al)) =
      eval (gate i).outputForm (build x w al) :=
  output_eq_of_bindings i _ _
    (HashAssignmentCompletenessSmall.hash_binding i _ (constant x w al))
    (hash_bindings x w al h i) (HashAssignmentCompletenessSmall.inputs i _)

theorem small_output_wire (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w)
    (i : Fin 54) :
    HashAssignmentCompletenessSmall.assignment i (build x w al)
        (CircuitAssemblyLayout.outputWire ⟨i.val + 1, by omega⟩) =
      build x w al (CircuitAssemblyLayout.outputWire ⟨i.val + 1, by omega⟩) := by
  have ho := small_output_eq x w al h i
  rw [CircuitAssemblyLayout.small_output_form] at ho
  simpa only [eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero] using ho

/-- Every small hash witness preserves the complete shared boundary. Its only
owned boundary wire is its output, which equals the seed's reference value. -/
theorem small_boundary (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w)
    (i : Fin 54) (wire : ℕ) (hb : CircuitAssemblyLayout.boundary wire) :
    HashAssignmentCompletenessSmall.assignment i (build x w al) wire =
      build x w al wire := by
  classical
  by_cases hw : CircuitAssemblyLayout.writes (CircuitAssemblyLayout.smallPart i) wire
  · have heq := CircuitAssemblyLayout.hash_boundary ⟨i.val + 1, by omega⟩ wire hw hb
    rw [heq]
    exact small_output_wire x w al h i
  · exact CircuitAssemblyLayout.small_preserves i (build x w al) wire hw

end MSP.Artifacts.SemanticAssignment
