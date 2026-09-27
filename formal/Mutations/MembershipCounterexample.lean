import Mutations.MembershipCertificate
import Mutations.MembershipRelation
import Mutations.Soundness

namespace MSP.Mutations.Membership

/-- A complete assignment satisfies every constraint of the compiled mutant,
but its actual projections violate canonical R3. Hence that mutant's C1 is false. -/
theorem c1_fails : ¬ C1For system :=
  refutes_c1 system table.toAssignment satisfied relation_fails

/-- Non-vacuous failure of the locked canonical relation, using the exact
mutant system and the original locked projections. -/
theorem counterexample : ∃ a : MSP.Assignment,
    system.Satisfied a ∧ ¬ R (MSP.stmtOf a) (MSP.witOf a) := by
  refine ⟨table.toAssignment, satisfied, ?_⟩
  unfold MSP.stmtOf MSP.witOf
  exact relation_fails

end MSP.Mutations.Membership
