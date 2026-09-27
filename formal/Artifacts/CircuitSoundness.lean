import Spec.Circuit
import Artifacts.NoteBindings
import Artifacts.SmallHashGatesComplete
import Artifacts.PublicSignals

/-! Soundness of the exact pinned constraint system. All individual hash,
arithmetic, selector and compression obligations are discharged before
instantiating the unchanged C1 proposition. Completeness and concrete
Groth16/verifier/chain bindings remain separate. -/

namespace MSP.Artifacts.CircuitSoundness

theorem relation_of_pinned_r1cs (a : Artifacts.Assignment)
    (h : Spend.system.Satisfied a) :
    R (ConcreteWitness.statementOf a) (ConcreteWitness.ofAssignment a) :=
  NoteBindings.relation_of_pinned_hash_instances a h
    (SmallHashGates.hash_bindings_of_system a h)

end MSP.Artifacts.CircuitSoundness

namespace MSP

/-- C1 for the complete pinned R1CS and its concrete statement/witness/public projections. -/
theorem c1 : C1 := by
  intro a h
  unfold Satisfied at h
  unfold stmtOf witOf publicOf
  exact ⟨Artifacts.CircuitSoundness.relation_of_pinned_r1cs a h,
    Artifacts.PublicSignals.compression_of_pinned_r1cs a h⟩

#print axioms c1

end MSP
