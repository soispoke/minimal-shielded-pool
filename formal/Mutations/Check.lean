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

end MSP.Mutations
