import Artifacts.CompressionData
import Spec.Hash
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The pinned compression prefix

Constraints 0..8 of the pinned R1CS force the gamma public wire to equal the
canonical polynomial evaluated at alpha + beta. This proof is about actual
extracted coefficient data. It does not identify beta with Poseidon, prove the
remaining constraints' relation to `R`, or replace `Spec.Circuit` declarations.
-/

namespace MSP.Artifacts.Compression

open CompressionData

/-- Candidate statement projection determined by the actual compression prefix.
The optimized circuit eliminated `fee`, whose field expression occurs in c1.
Consistency with all other circuit gadgets remains to be established. -/
def statement (w : Assignment) : Statement :=
  ⟨w 99, w 100, w 101, w 102, w 4, w 5, w 96,
   w 10 + w 11 - w 94 - w 95 - w 96, w 97, w 98⟩

private theorem coefficient_neg_one :
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 : F) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  norm_num
  exact ZMod.natCast_self p

/-- Every assignment satisfying the nine concrete constraints has the specified
compressed gamma. The beta wire's Poseidon binding is a separate obligation. -/
theorem gamma_of_constraints (w : Assignment)
    (h : ∀ c ∈ constraints, c.Holds w) :
    w 2 = MSP.γ (statement w) (w 3 + w 1) := by
  have h0 := h c0 (by simp [constraints])
  have h1 := h c1 (by simp [constraints])
  have h2 := h c2 (by simp [constraints])
  have h3 := h c3 (by simp [constraints])
  have h4 := h c4 (by simp [constraints])
  have h5 := h c5 (by simp [constraints])
  have h6 := h c6 (by simp [constraints])
  have h7 := h c7 (by simp [constraints])
  have h8 := h c8 (by simp [constraints])
  simp [Constraint.Holds, LinearCombination.eval, c0, c1, c2, c3, c4, c5, c6, c7, c8,
    coefficient_neg_one] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [MSP.γ, Statement.vec, statement, Fin.sum_univ_succ]
  linear_combination
    (w 3 + w 1)^8 * h0 + (w 3 + w 1)^7 * h1 +
    (w 3 + w 1)^6 * h2 + (w 3 + w 1)^5 * h3 +
    (w 3 + w 1)^4 * h4 + (w 3 + w 1)^3 * h5 +
    (w 3 + w 1)^2 * h6 + (w 3 + w 1) * h7 + h8

/-- Any concrete system containing this exact extracted prefix inherits its
compression equation. The membership premise must be supplied by the full
artifact binding; it is not assumed globally. -/
theorem gamma_of_system {s : System} (w : Assignment)
    (contains : ∀ c ∈ constraints, c ∈ s.constraints) (h : s.Satisfied w) :
    w 2 = MSP.γ (statement w) (w 3 + w 1) :=
  gamma_of_constraints w (fun c hc => h.2 c (contains c hc))

end MSP.Artifacts.Compression
