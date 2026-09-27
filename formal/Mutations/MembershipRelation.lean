import Mutations.MembershipTable
import Artifacts.Witness
import Proofs.NonVacuityPoseidon
import Proofs.C6

namespace MSP.Mutations.Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def statement : Statement := Artifacts.ConcreteWitness.statementOf table.toAssignment
def witness : Witness := Artifacts.ConcreteWitness.ofAssignment table.toAssignment

theorem first_value : witness.v 0 = 2 := by decide
theorem first_key : witness.sk 0 = 1 := by decide
theorem first_rho : witness.ρ 0 = 1 := by decide
theorem first_index : witness.idx 0 = 0 := by decide
theorem statement_root : statement.root = 0 := by decide

theorem first_leaf : witness.leaf 0 = NonVacuity.fixtureLeaf := by
  simp only [Witness.leaf, first_key, first_rho, first_value]
  rfl

theorem first_siblings (l : Fin DEPTH) : witness.sib 0 l = Z l.val := by
  rw [← zero_constants l.val l.isLt]
  fin_cases l <;> decide

/-- The positive input is the checked W1 note with its real path, whereas
the mutant's public root is zero. No hash assumption is needed to refute R3. -/
theorem relation_fails : ¬ R statement witness := by
  intro h
  have hv : witness.v 0 ≠ 0 := by rw [first_value]; decide
  have hm := h.2.2.2.1 0 hv
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
