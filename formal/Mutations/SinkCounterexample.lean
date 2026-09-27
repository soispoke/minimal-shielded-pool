import Mutations.SinkCertificate
import Mutations.SinkRelation
import Mutations.Soundness

namespace MSP.Mutations.Sink

/-- Every compiled mutant constraint holds, but the actual projections
violate the canonical spend relation. Therefore its full C1 is false. -/
theorem c1_fails : ¬ C1For system :=
  refutes_c1 system table.toAssignment satisfied relation_fails

/-- Non-vacuous failure of the locked canonical relation, using the exact
mutant system and the original locked projections. -/
theorem counterexample : ∃ a : MSP.Assignment,
    system.Satisfied a ∧ ¬ R (MSP.stmtOf a) (MSP.witOf a) := by
  refine ⟨table.toAssignment, satisfied, ?_⟩
  unfold MSP.stmtOf MSP.witOf
  exact relation_fails


/-- The clause that fails is R7: a zero-value first output whose `inner` is not 1. -/
theorem clause_fails : ∃ a : MSP.Assignment, system.Satisfied a ∧
    (MSP.witOf a).ov 0 = 0 ∧ (MSP.witOf a).oi 0 ≠ 1 := by
  refine ⟨table.toAssignment, satisfied, ?_⟩
  unfold MSP.witOf
  refine ⟨first_output_zero, ?_⟩
  rw [show Artifacts.ConcreteWitness.ofAssignment table.toAssignment = witness from rfl,
    first_output_inner]
  decide

end MSP.Mutations.Sink
