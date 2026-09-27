import Artifacts.HashAssignmentCompletenessBetaAffine
import Artifacts.Compression

/-! A complete assignment for the 459 pinned beta constraints. Starting from
arbitrary ambient statement wires, the construction fills the exact optimized
hash trace, preserves every unrelated wire, and produces the ordinary H10
reference output. Only the ambient constant wire is required to equal one. -/

namespace MSP.Artifacts.HashAssignmentCompletenessBeta

open BetaGates HashAssignmentCompleteness HashAssignmentCompletenessBetaData

set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

noncomputable def complete (ambient : Assignment) : Assignment :=
  buildAssignment (g := circuit) scheme powers AssignmentRecoveryBetaData.plan stages ambient

theorem complete_zero (ambient : Assignment) : complete ambient 0 = ambient 0 := by
  unfold complete
  exact buildAssignment_zero (g := circuit) scheme powers AssignmentRecoveryBetaData.plan stages ambient

/-- Exactly wire one and the contiguous internal beta wires may change. -/
theorem complete_preserves (ambient : Assignment) (wire : ℕ)
    (h : wire ≠ 1 ∧ (wire < 111 ∨ 569 ≤ wire)) :
    complete ambient wire = ambient wire := by
  apply buildAssignment_preserves (g := circuit) scheme powers AssignmentRecoveryBetaData.plan stages ambient wire
  · rw [AssignmentRecoveryBetaData.written_eq]
    simp only [List.mem_cons, List.mem_range', not_or]
    constructor
    · exact h.1
    · omega
  · intro k
    have ht := k.1.isLt
    have hj := k.2.isLt
    change k.1.val < 153 at ht
    change 263 + 2 * k.1.val + k.2.val ≠ wire
    omega

/-- All 459 original beta constraints hold under this construction. -/
theorem complete_holds (ambient : Assignment) (hzero : ambient 0 = 1) :
    ∀ c ∈ BetaGatesData.constraints, c.Holds (complete ambient) := by
  unfold complete
  exact (buildAssignment_complete (g := circuit) scheme affine signs powers AssignmentRecoveryBetaData.plan
    separate stages recovery ambient hzero).1

private theorem statement_inputs (ambient : Assignment) :
    ambientInputs circuit ambient = (Compression.statement ambient).vec := by
  funext j
  change Fin 10 at j
  fin_cases j <;>
    simp [ambientInputs, circuit, BetaGatesCertificates.statementForms, eval,
      Compression.statement, Statement.vec]
  ring

/-- The output equals canonical D2 Poseidon over the exact ten ambient statement fields. -/
theorem complete_beta (ambient : Assignment) (hzero : ambient 0 = 1) :
    complete ambient 1 = MSP.β (Compression.statement ambient) := by
  have ho := (buildAssignment_complete (g := circuit) scheme affine signs powers AssignmentRecoveryBetaData.plan
    separate stages recovery ambient hzero).2
  change eval [(1, 1)] (complete ambient) = scheme.hash (ambientInputs circuit ambient) at ho
  simp only [eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero] at ho
  rw [ho, statement_inputs, scheme_hash, MSP.Poseidon.Optimized.hash10_eq_reference]
  unfold MSP.β MSP.H10
  rfl

/-- The construction preserves all ten fields whose digest it computes. -/
theorem statement_preserved (ambient : Assignment) :
    Compression.statement (complete ambient) = Compression.statement ambient := by
  have hp (wire : ℕ) (h : wire < 111) (hn : wire ≠ 1) :
      complete ambient wire = ambient wire := complete_preserves ambient wire ⟨hn, Or.inl h⟩
  simp [Compression.statement, hp 99 (by decide) (by decide), hp 100 (by decide) (by decide),
    hp 101 (by decide) (by decide), hp 102 (by decide) (by decide),
    hp 4 (by decide) (by decide), hp 5 (by decide) (by decide), hp 96 (by decide) (by decide),
    hp 10 (by decide) (by decide), hp 11 (by decide) (by decide),
    hp 94 (by decide) (by decide), hp 95 (by decide) (by decide),
    hp 97 (by decide) (by decide), hp 98 (by decide) (by decide)]

end MSP.Artifacts.HashAssignmentCompletenessBeta
