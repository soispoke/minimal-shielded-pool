import Artifacts.RangeAssignmentCompleteness
import Artifacts.Witness

namespace MSP.Artifacts.RangeAssignmentCompleteness

/-- The canonical relation supplies precisely the eight range bounds. -/
theorem bounds_of_relation (a : Assignment)
    (h : R (ConcreteWitness.statementOf a) (ConcreteWitness.ofAssignment a)) : Bounds a := by
  rcases h with ⟨_, _, _, _, _, _, hranges, _, _, _, _, _, hrcp, _, hauth, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hrcp, hauth⟩
  · exact hranges _ (by simp [ConcreteWitness.ofAssignment, ConcreteWitness.statementOf, Compression.statement, PathBitsData.valueWire, PathBitsData.outputValueWire])
  · exact hranges _ (by simp [ConcreteWitness.ofAssignment, ConcreteWitness.statementOf, Compression.statement, PathBitsData.valueWire, PathBitsData.outputValueWire])
  · exact hranges _ (by simp [ConcreteWitness.ofAssignment, ConcreteWitness.statementOf, Compression.statement, PathBitsData.valueWire, PathBitsData.outputValueWire])
  · exact hranges _ (by simp [ConcreteWitness.ofAssignment, ConcreteWitness.statementOf, Compression.statement, PathBitsData.valueWire, PathBitsData.outputValueWire])
  · exact hranges _ (by simp [ConcreteWitness.ofAssignment, ConcreteWitness.statementOf, Compression.statement, PathBitsData.valueWire, PathBitsData.outputValueWire])
  · exact hranges _ (by simp [ConcreteWitness.ofAssignment, ConcreteWitness.statementOf, Compression.statement, PathBitsData.valueWire, PathBitsData.outputValueWire])

theorem complete_holds_of_relation (a : Assignment) (hz : a 0 = 1)
    (h : R (ConcreteWitness.statementOf a) (ConcreteWitness.ofAssignment a)) :
    ∀ c ∈ constraints, c.Holds (complete a) :=
  complete_holds a hz (bounds_of_relation a h)

#print axioms complete_holds_of_relation
end MSP.Artifacts.RangeAssignmentCompleteness
