import Proofs.NonVacuityTrace
import Artifacts.CircuitCompleteness

/-! W1's ideal verifier accepts exactly the public signals of satisfying
assignments for every proof byte string. Its extractor prefers the fixture's
known assignment, then chooses a witness for any other accepted public input.
No property of a cryptographic verifier is assumed by this construction. -/

namespace MSP.NonVacuity

noncomputable section
open Classical

def idealPool (A c : ℕ) (preferred : Assignment) : Pool where
  A := A
  c := c
  verifies := fun _ pub => ∃ a, Satisfied a ∧ publicOf a = pub
  ext := fun _ pub =>
    if pub = publicOf preferred then preferred
    else if h : ∃ a, Satisfied a ∧ publicOf a = pub then h.choose
    else preferred

theorem idealPool_exact (A c : ℕ) (preferred : Assignment) (π : List UInt8)
    (pub : F × F × F) :
    (idealPool A c preferred).verifies π pub ↔
      ∃ a, Satisfied a ∧ publicOf a = pub := Iff.rfl

theorem idealPool_ideal (A c : ℕ) (preferred : Assignment) (hs : Satisfied preferred) :
    IdealVerifier (idealPool A c preferred) := by
  intro π pub h
  change Satisfied (if pub = publicOf preferred then preferred
      else if h : ∃ a, Satisfied a ∧ publicOf a = pub then h.choose else preferred) ∧ _
  by_cases he : pub = publicOf preferred
  · simpa only [he, ite_eq_left, idealPool] using And.intro hs he.symm
  · have hc : ∃ a, Satisfied a ∧ publicOf a = pub := h
    simpa only [he, ite_false, dite_eq_left hc, idealPool] using hc.choose_spec

theorem idealPool_preferred (A c : ℕ) (preferred : Assignment) (π : List UInt8) :
    (idealPool A c preferred).ext π (publicOf preferred) = preferred := by
  simp [idealPool]

theorem idealPool_accepts_preferred (A c : ℕ) (preferred : Assignment)
    (hs : Satisfied preferred) (π : List UInt8) :
    (idealPool A c preferred).verifies π (publicOf preferred) := ⟨preferred, hs, rfl⟩

/-- C1c supplies an actual assignment to the pinned R1CS, with the intended
statement, witness, and alpha. The verifier construction above can use it
without a separate witness-existence or extraction premise. -/
theorem idealPool_of_relation (A c : ℕ) (x : Statement) (w : Witness) (hR : R x w) :
    ∃ (a : Assignment), Satisfied a ∧ stmtOf a = x ∧ witOf a = w ∧
      publicOf a = (β x, γ x (α x + β x), α x) ∧
      IdealVerifier (idealPool A c a) := by
  obtain ⟨a, hs, hx, hw, hp⟩ := c1c x w (α x) hR
  exact ⟨a, hs, hx, hw, hp, idealPool_ideal A c a hs⟩

end
end MSP.NonVacuity
