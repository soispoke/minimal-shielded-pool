import Mutations.DuplicateTable
import Artifacts.Witness

namespace MSP.Mutations.Duplicate

set_option maxRecDepth 100000
def statement : Statement := Artifacts.ConcreteWitness.statementOf table.toAssignment
def witness : Witness := Artifacts.ConcreteWitness.ofAssignment table.toAssignment

theorem equal_nullifiers : statement.nf1 = statement.nf2 := by decide

/-- The two actual statement nullifiers coincide, violating canonical R8. -/
theorem relation_fails : ¬ R statement witness := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, distinct, _⟩
  exact distinct equal_nullifiers

end MSP.Mutations.Duplicate
