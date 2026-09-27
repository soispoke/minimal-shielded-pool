import Artifacts.SinkGatesData
import Artifacts.Spend
import Proofs.CircuitGadgets

/-!
# Output sink rules from the pinned R1CS

The actual IsZero/IsEqual gadgets and their controlling multiplications imply
R7 for the retained output-inner and output-value wires. This holds for every
assignment satisfying the full R1CS, without trusting its witness generator.
Binding the remaining relation and opaque circuit declarations is separate.
-/

namespace MSP.Artifacts.SinkGates

open SinkGatesData

theorem controls_eq_slice : controls = (Spend.group1.drop 212).take 6 := rfl

theorem gadgets_eq_slice : gadgets = (Spend.group54.drop 32).take 12 := rfl

private theorem control_mem {c : Constraint} (hc : c ∈ controls) :
    c ∈ Spend.system.constraints := by
  rw [controls_eq_slice] at hc
  exact List.mem_flatten.mpr
    ⟨Spend.group1, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem gadget_mem {c : Constraint} (hc : c ∈ gadgets) :
    c ∈ Spend.system.constraints := by
  rw [gadgets_eq_slice] at hc
  exact List.mem_flatten.mpr
    ⟨Spend.group54, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem neg_one :
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 : F) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  norm_num
  exact ZMod.natCast_self p

private theorem neg_two :
    (21888242871839275222246405745257275088548364400416034343698204186575808495615 : F) = -2 := by
  apply eq_neg_of_add_eq_zero_left
  norm_num
  exact ZMod.natCast_self p

private theorem sink_rules_of_equations (value inner target zero eq1 eq2 inv0 inv1 inv2 : F)
    (hzdef : value * inv0 = 1 - zero) (hzgate : value * zero = 0)
    (h1def : (1 - inner) * inv1 = 1 - eq1) (h1gate : (1 - inner) * eq1 = 0)
    (h2def : (2 - inner) * inv2 = 1 - eq2) (h2gate : (2 - inner) * eq2 = 0)
    (hsink : (inner - target) * zero = 0)
    (hexcl1 : (1 - zero) * eq1 = 0) (hexcl2 : (1 - zero) * eq2 = 0) :
    (value = 0 → inner = target) ∧ (value ≠ 0 → inner ≠ 1 ∧ inner ≠ 2) := by
  have hz := MSP.isZero_sound value inv0 zero (by linear_combination hzdef) hzgate
  have h1 := (MSP.isZero_sound (1 - inner) inv1 eq1
    (by linear_combination h1def) h1gate).1
  have h2 := (MSP.isZero_sound (2 - inner) inv2 eq2
    (by linear_combination h2def) h2gate).1
  constructor
  · intro hv
    rw [hz.1.mpr hv, mul_one] at hsink
    exact sub_eq_zero.mp hsink
  · intro hv
    have hz0 := hz.2.mpr hv
    rw [hz0, sub_zero, one_mul] at hexcl1 hexcl2
    constructor
    · intro hi
      have he := h1.mpr (by rw [hi, sub_self])
      exact zero_ne_one (hexcl1.symm.trans he)
    · intro hi
      have he := h2.mpr (by rw [hi, sub_self])
      exact zero_ne_one (hexcl2.symm.trans he)

/-- The first zero output has inner 1; a nonzero output uses neither reserved inner. -/
theorem first_output_sink_rules (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 94 = 0 → w 92 = 1) ∧ (w 94 ≠ 0 → w 92 ≠ 1 ∧ w 92 ≠ 2) := by
  have h468 := h.2 _ (control_mem (c := c468) (by simp [controls]))
  have h469 := h.2 _ (control_mem (c := c469) (by simp [controls]))
  have h470 := h.2 _ (control_mem (c := c470) (by simp [controls]))
  have h13856 := h.2 _ (gadget_mem (c := c13856) (by simp [gadgets]))
  have h13857 := h.2 _ (gadget_mem (c := c13857) (by simp [gadgets]))
  have h13860 := h.2 _ (gadget_mem (c := c13860) (by simp [gadgets]))
  have h13861 := h.2 _ (gadget_mem (c := c13861) (by simp [gadgets]))
  have h13864 := h.2 _ (gadget_mem (c := c13864) (by simp [gadgets]))
  have h13865 := h.2 _ (gadget_mem (c := c13865) (by simp [gadgets]))
  simp only [c468, c469, c470, c13856, c13857, c13860, c13861, c13864, c13865,
    Constraint.Holds, LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, Nat.cast_ofNat, neg_one,
    h.1, one_mul, mul_one, neg_one_mul, add_zero] at h468 h469 h470 h13856 h13857 h13860 h13861 h13864 h13865
  apply sink_rules_of_equations (w 94) (w 92) 1
    (w 13912) (w 13904) (w 13908) (w 13913) (w 13905) (w 13909)
  · linear_combination h13864
  · exact h13865
  · linear_combination h13856
  · linear_combination h13857
  · linear_combination h13860
  · linear_combination h13861
  · linear_combination h468
  · linear_combination h469
  · linear_combination h470

/-- The second zero output has inner 2; a nonzero output uses neither reserved inner. -/
theorem second_output_sink_rules (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 95 = 0 → w 93 = 2) ∧ (w 95 ≠ 0 → w 93 ≠ 1 ∧ w 93 ≠ 2) := by
  have h471 := h.2 _ (control_mem (c := c471) (by simp [controls]))
  have h472 := h.2 _ (control_mem (c := c472) (by simp [controls]))
  have h473 := h.2 _ (control_mem (c := c473) (by simp [controls]))
  have h13858 := h.2 _ (gadget_mem (c := c13858) (by simp [gadgets]))
  have h13859 := h.2 _ (gadget_mem (c := c13859) (by simp [gadgets]))
  have h13862 := h.2 _ (gadget_mem (c := c13862) (by simp [gadgets]))
  have h13863 := h.2 _ (gadget_mem (c := c13863) (by simp [gadgets]))
  have h13866 := h.2 _ (gadget_mem (c := c13866) (by simp [gadgets]))
  have h13867 := h.2 _ (gadget_mem (c := c13867) (by simp [gadgets]))
  simp only [c471, c472, c473, c13858, c13859, c13862, c13863, c13866, c13867,
    Constraint.Holds, LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, Nat.cast_ofNat, neg_one, neg_two,
    h.1, one_mul, mul_one, neg_one_mul, add_zero] at h471 h472 h473 h13858 h13859 h13862 h13863 h13866 h13867
  apply sink_rules_of_equations (w 95) (w 93) 2
    (w 13914) (w 13906) (w 13910) (w 13915) (w 13907) (w 13911)
  · linear_combination h13866
  · exact h13867
  · linear_combination h13858
  · linear_combination h13859
  · linear_combination h13862
  · linear_combination h13863
  · linear_combination h471
  · linear_combination h472
  · linear_combination h473

/-- R7 for the raw output projection of every full satisfying assignment. -/
theorem sink_rules (w : Assignment) (h : Spend.system.Satisfied w) (k : Fin 2) :
    (w (94 + k.val) = 0 → w (92 + k.val) = ((k.val + 1 : ℕ) : F)) ∧
    (w (94 + k.val) ≠ 0 → w (92 + k.val) ≠ 1 ∧ w (92 + k.val) ≠ 2) := by
  fin_cases k
  · simpa using first_output_sink_rules w h
  · simpa using second_output_sink_rules w h

#print axioms sink_rules

end MSP.Artifacts.SinkGates
