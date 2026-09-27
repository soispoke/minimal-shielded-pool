import Mutations.SinkTable
import Artifacts.Witness

namespace MSP.Mutations.Sink

set_option maxRecDepth 100000
def statement : Statement := Artifacts.ConcreteWitness.statementOf table.toAssignment
def witness : Witness := Artifacts.ConcreteWitness.ofAssignment table.toAssignment

theorem first_output_zero : witness.ov 0 = 0 := by decide
theorem first_output_inner : witness.oi 0 = 3 := by decide

/-- Output zero has value zero but inner 3 instead of its designated inner 1. -/
theorem relation_fails : ¬ R statement witness := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, sinks, _⟩
  have hs := (sinks 0).1 first_output_zero
  rw [first_output_inner] at hs
  exact (by decide : (3 : F) ≠ 1) hs

end MSP.Mutations.Sink
