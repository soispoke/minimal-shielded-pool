import Spec.Relation
import Artifacts.Witness

/-!
# C1 and C1c: the circuit

The circuit definitions below use the pinned `build/spend.r1cs`: a generated
file lists its constraints over `F` and names signals through a symbol file
that recompiling the pinned circuit produces. `formal/tools/r1cs_artifact.py
--check-lean` regenerates that file from the artifact (SHA-256
`e2f6fc89bc0e4782…`) and compares it byte for byte, and CI's `formal` job runs
it with the symbol file from recompiling the circuit.
-/

namespace MSP

def AssignmentImpl : NonemptyType.{0} :=
  ⟨Artifacts.Assignment, ⟨fun _ => 0⟩⟩
/-- An assignment to every wire of `spend.r1cs`. -/
def Assignment : Type := AssignmentImpl.type
instance : Nonempty Assignment := AssignmentImpl.property
noncomputable instance : Inhabited Assignment := Classical.inhabited_of_nonempty inferInstance
/-- Wire 0, the constant wire, equals 1 and every constraint of `spend.r1cs` holds. -/
@[irreducible] def Satisfied (a : Assignment) : Prop := Artifacts.Spend.system.Satisfied a
/-- The statement signals `stmt[0..9]`. -/
@[irreducible] def stmtOf (a : Assignment) : Statement := Artifacts.ConcreteWitness.statementOf a
/-- The private input signals, with indices read from the path bits. -/
@[irreducible] def witOf (a : Assignment) : Witness := Artifacts.ConcreteWitness.ofAssignment a
/-- The public signals in the verifier's order `(β, γ, α)`. -/
@[irreducible] def publicOf (a : Assignment) : F × F × F := Artifacts.ConcreteWitness.publicOf a

/-- C1. Every satisfying assignment is a valid spend with correct public signals. -/
def C1 : Prop :=
  ∀ a, Satisfied a →
    R (stmtOf a) (witOf a) ∧
    (publicOf a).1 = β (stmtOf a) ∧
    (publicOf a).2.1 = γ (stmtOf a) ((publicOf a).2.2 + (publicOf a).1)

/-- C1c. Every valid spend has a satisfying assignment, for every `α`. -/
def C1c : Prop :=
  ∀ (x : Statement) (w : Witness) (al : F), R x w →
    ∃ a, Satisfied a ∧ stmtOf a = x ∧ witOf a = w ∧
      publicOf a = (β x, γ x (al + β x), al)

/-- Groth16's verification for the committed key in
`contracts/vectors/spend_vkey.json`: the eight proof words are coordinates below
`q` of points `A` and `C` of G1 and `B` of G2, in EIP-197's encoding (each G2
coordinate imaginary part first), on the curves, in the prime-order
subgroups and none at infinity, and the pairing equation holds for the public
signals. Step 5 defines it from the key. -/
opaque Groth16Accepts : List UInt8 → F × F × F → Prop

end MSP
