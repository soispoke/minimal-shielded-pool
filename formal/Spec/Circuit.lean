import Spec.Relation

/-!
# C1 and C1c: the circuit

Step 3 binds these declarations to the pinned `build/spend.r1cs`: a generated
file lists its constraints over `F`, reads the named signals through
`build/spend.sym`, and CI checks the generated file against the artifact's
SHA-256 (`e2f6fc89bc0e4782…`).
-/

namespace MSP

opaque AssignmentImpl : NonemptyType.{0}
/-- An assignment to every wire of `spend.r1cs`. -/
def Assignment : Type := AssignmentImpl.type
instance : Nonempty Assignment := AssignmentImpl.property
noncomputable instance : Inhabited Assignment := Classical.inhabited_of_nonempty inferInstance
/-- Wire 0, the constant wire, equals 1 and every constraint of `spend.r1cs` holds. -/
opaque Satisfied : Assignment → Prop
/-- The statement signals `stmt[0..9]`. -/
opaque stmtOf : Assignment → Statement
/-- The private input signals, with indices read from the path bits. -/
opaque witOf : Assignment → Witness
/-- The public signals in the verifier's order `(β, γ, α)`. -/
opaque publicOf : Assignment → F × F × F

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

end MSP
