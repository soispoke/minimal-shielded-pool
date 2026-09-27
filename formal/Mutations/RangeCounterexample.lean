import Mutations.RangeCertificate
import Mutations.RangeRelation
import Mutations.Soundness

namespace MSP.Mutations.Range

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


/-- The clause that fails is R5: the first input value is not below `2 ^ 128`. -/
theorem clause_fails : ∃ a : MSP.Assignment, system.Satisfied a ∧
    ¬ ((MSP.witOf a).v 0).val < 2 ^ 128 := by
  refine ⟨table.toAssignment, satisfied, ?_⟩
  unfold MSP.witOf
  have := first_value
  simp only [witness] at this
  omega

end MSP.Mutations.Range
