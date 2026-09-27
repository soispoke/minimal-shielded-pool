import Mutations.DuplicateCertificate
import Mutations.DuplicateRelation
import Mutations.Soundness

namespace MSP.Mutations.Duplicate

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


/-- The clause that fails is R8: the two nullifiers are equal. -/
theorem clause_fails : ∃ a : MSP.Assignment, system.Satisfied a ∧
    (MSP.stmtOf a).nf1 = (MSP.stmtOf a).nf2 := by
  refine ⟨table.toAssignment, satisfied, ?_⟩
  unfold MSP.stmtOf
  exact equal_nullifiers

end MSP.Mutations.Duplicate
