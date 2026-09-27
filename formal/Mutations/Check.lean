import Artifacts.R1CS

/-! A finite, kernel-computable checker for explicit R1CS assignments.
The reflection theorem uses the same constraint semantics as the C1 proof. -/

namespace MSP.Mutations

open Artifacts

def assignment (values : Array ℕ) : Assignment :=
  fun i => (values[i]?.getD 0 : F)

def checkConstraint (values : Array ℕ) (c : Constraint) : Bool :=
  decide (c.a.eval (assignment values) * c.b.eval (assignment values) =
    c.c.eval (assignment values))

def checkConstraints (values : Array ℕ) (cs : List Constraint) : Bool :=
  cs.all (checkConstraint values)

theorem holds_of_checkConstraint (values : Array ℕ) (c : Constraint)
    (h : checkConstraint values c = true) : c.Holds (assignment values) := by
  unfold Constraint.Holds
  exact of_decide_eq_true h

theorem holds_of_checkConstraints (values : Array ℕ) (cs : List Constraint)
    (h : checkConstraints values cs = true) :
    ∀ c ∈ cs, c.Holds (assignment values) := by
  intro c hc
  exact holds_of_checkConstraint values c (List.all_eq_true.mp h c hc)

theorem satisfied_of_blocks (values : Array ℕ) (blocks : List (List Constraint))
    (wires : ℕ) (hzero : assignment values 0 = 1)
    (h : ∀ cs ∈ blocks, checkConstraints values cs = true) :
    (System.mk wires blocks.flatten).Satisfied (assignment values) := by
  refine ⟨hzero, ?_⟩
  intro c hc
  obtain ⟨cs, hs, hc⟩ := List.mem_flatten.mp hc
  exact holds_of_checkConstraints values cs (h cs hs) c hc


/-- A binary table indexed by successive low bits. Unlike a flat kernel array,
lookup follows only logarithmically many constructors. Values beyond its full
power-of-two shape are zero. The shape is explicit in generated certificates. -/
inductive WireTable where
  | leaf (value : ℕ)
  | branch (even odd : WireTable)

def WireTable.get : WireTable → ℕ → ℕ
  | .leaf value, i => if i = 0 then value else 0
  | .branch even odd, i =>
      if i % 2 = 0 then even.get (i / 2) else odd.get (i / 2)

def WireTable.toAssignment (t : WireTable) : Assignment := fun i => (t.get i : F)

def checkAssignmentConstraint (w : Assignment) (c : Constraint) : Bool :=
  decide (c.a.eval w * c.b.eval w = c.c.eval w)

def checkAssignmentConstraints (w : Assignment) (cs : List Constraint) : Bool :=
  cs.all (checkAssignmentConstraint w)

theorem holds_of_checked_assignment (w : Assignment) (cs : List Constraint)
    (h : checkAssignmentConstraints w cs = true) : ∀ c ∈ cs, c.Holds w := by
  intro c hc
  have he := List.all_eq_true.mp h c hc
  unfold Constraint.Holds
  exact of_decide_eq_true he

theorem satisfied_of_checked_blocks (w : Assignment) (blocks : List (List Constraint))
    (wires : ℕ) (hzero : w 0 = 1)
    (h : ∀ cs ∈ blocks, checkAssignmentConstraints w cs = true) :
    (System.mk wires blocks.flatten).Satisfied w := by
  refine ⟨hzero, ?_⟩
  intro c hc
  obtain ⟨cs, hs, hc⟩ := List.mem_flatten.mp hc
  exact holds_of_checked_assignment w cs (h cs hs) c hc

end MSP.Mutations
