import Spec.Circuit

namespace MSP.Mutations

/-- Exactly C1 with the R1CS replaced and the canonical projections retained.
The exporter checks those wire numbers against every mutated symbol file. -/
def C1For (s : Artifacts.System) : Prop :=
  ∀ a : MSP.Assignment, s.Satisfied a →
    R (stmtOf a) (witOf a) ∧
    (publicOf a).1 = β (stmtOf a) ∧
    (publicOf a).2.1 = γ (stmtOf a) ((publicOf a).2.2 + (publicOf a).1)

theorem original_c1_iff : C1For Artifacts.Spend.system ↔ C1 := by
  unfold C1For C1 Satisfied
  rfl

theorem refutes_c1 (s : Artifacts.System) (a : Artifacts.Assignment)
    (hs : s.Satisfied a)
    (hr : ¬ R (Artifacts.ConcreteWitness.statementOf a)
      (Artifacts.ConcreteWitness.ofAssignment a)) : ¬ C1For s := by
  intro h
  apply hr
  have hp := (h a hs).1
  unfold MSP.stmtOf MSP.witOf at hp
  exact hp

end MSP.Mutations
