import Mutations.RangeTable
import Artifacts.Witness

namespace MSP.Mutations.Range

set_option maxRecDepth 100000
def statement : Statement := Artifacts.ConcreteWitness.statementOf table.toAssignment
def witness : Witness := Artifacts.ConcreteWitness.ofAssignment table.toAssignment

theorem first_value : (witness.v 0).val = 2 ^ 128 := by decide

/-- The complete witness has a first input outside the required 128-bit range. -/
theorem relation_fails : ¬ R statement witness := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, bounds, _⟩
  have hb := bounds (witness.v 0) (by simp)
  rw [first_value] at hb
  exact Nat.lt_irrefl _ hb

end MSP.Mutations.Range
