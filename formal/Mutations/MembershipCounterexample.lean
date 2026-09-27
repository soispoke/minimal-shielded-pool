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


/-- The clause that fails is R3: a nonzero-value input whose Merkle path does
not reach the statement's root. -/
theorem clause_fails : ∃ a : MSP.Assignment, system.Satisfied a ∧
    ∃ k, (MSP.witOf a).v k ≠ 0 ∧
      MR ((MSP.witOf a).leaf k) ((MSP.witOf a).idx k) ((MSP.witOf a).sib k) ≠ (MSP.stmtOf a).root := by
  refine ⟨table.toAssignment, satisfied, 0, ?_, ?_⟩
  · unfold MSP.witOf
    change witness.v 0 ≠ 0
    rw [first_value]; decide
  · unfold MSP.witOf MSP.stmtOf
    change MR (witness.leaf 0) (witness.idx 0) (witness.sib 0) ≠ statement.root
    intro hm
    rw [first_leaf, first_index, statement_root] at hm
    have hs : witness.sib 0 = siblingsOf [NonVacuity.fixtureLeaf] 0 := by
      funext l
      rw [first_siblings, NonVacuity.siblings_singleton_zero]
    have hp : MR NonVacuity.fixtureLeaf 0 (siblingsOf [NonVacuity.fixtureLeaf] 0) =
        TR [NonVacuity.fixtureLeaf] := by
      simpa using MR_siblingsOf [NonVacuity.fixtureLeaf] 0 (by decide)
    rw [hs, hp] at hm
    exact NonVacuity.fixture_root_ne_zero hm

end MSP.Mutations.Membership
