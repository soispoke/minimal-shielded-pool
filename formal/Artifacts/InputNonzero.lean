import Artifacts.Spend
import Proofs.CircuitArithmetic
import Proofs.CircuitGadgets

/-! The actual nonzero-input constraint of the pinned R1CS.
The source's IsZero output has been eliminated, leaving this inverse equation.
No witness-generator behavior or high-level spend relation is assumed. -/

namespace MSP.Artifacts.InputNonzero

/-- Constraint 635, checked against the complete generated data below. -/
def constraint : Constraint := ⟨[(10, 1), (11, 1)], [(729, 1)], [(0, 1)]⟩

theorem constraint_mem : constraint ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group2, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk79, by simp, by simp [Spend.chunk79, constraint]⟩

theorem sum_ne_zero (w : Assignment) (h : Spend.system.Satisfied w) :
    w 10 + w 11 ≠ 0 := by
  have hc := h.2 _ constraint_mem
  simp only [constraint, Constraint.Holds, LinearCombination.eval, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] at hc
  rw [h.1] at hc
  intro hz
  rw [hz, zero_mul] at hc
  exact zero_ne_one hc

/-- R6's positive integer input value, derived from the pinned constraint. -/
theorem positive_input_value (w : Assignment) (h : Spend.system.Satisfied w) :
    0 < (w 10).val + (w 11).val :=
  MSP.input_sum_pos _ _ (sum_ne_zero w h)

#print axioms sum_ne_zero
#print axioms positive_input_value

end MSP.Artifacts.InputNonzero
