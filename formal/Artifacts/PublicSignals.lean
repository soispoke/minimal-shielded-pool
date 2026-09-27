import Artifacts.BetaGates
import Artifacts.Witness
import Poseidon.OptimizedEquivalence

/-! Both compression outputs of the full pinned circuit, under the same
concrete statement and public-wire projections. `CircuitSoundness`
combines them with the relation to prove C1. -/

namespace MSP.Artifacts.PublicSignals

attribute [local irreducible] MSP.Poseidon.hash10 MSP.Poseidon.Optimized.hash10

theorem beta_of_pinned_r1cs (a : Assignment) (h : Spend.system.Satisfied a) :
    a 1 = MSP.β (Compression.statement a) := by
  unfold MSP.β MSP.H10
  exact (BetaGates.beta_of_system a h).trans
    (MSP.Poseidon.Optimized.hash10_eq_reference (Compression.statement a).vec)

theorem compression_of_pinned_r1cs (a : Assignment) (h : Spend.system.Satisfied a) :
    let x := ConcreteWitness.statementOf a
    let pub := ConcreteWitness.publicOf a
    pub.1 = MSP.β x ∧ pub.2.1 = MSP.γ x (pub.2.2 + pub.1) :=
  ⟨beta_of_pinned_r1cs a h, ConcreteWitness.public_gamma a h⟩

#print axioms beta_of_pinned_r1cs
#print axioms compression_of_pinned_r1cs

end MSP.Artifacts.PublicSignals
