import Artifacts.SinkGates
import Artifacts.InputCompleteness
import Artifacts.Witness

/-! Construct every inverse/IsZero auxiliary wire of the pinned circuit from
its non-hash relation conditions. Only the listed 19 auxiliaries are written.
The resulting assignment satisfies the 26 actual control constraints; the
remaining range, path, and hash fragments are assembled separately. -/

namespace MSP.Artifacts.ControlCompleteness

open SinkGatesData

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The output of the canonical IsZero witness. -/
def zeroFlag (x : F) : F := if x = 0 then 1 else 0

/-- Exactly the retained inverse and IsZero output wires. -/
def writeSet : Finset ℕ := {728, 729, 13904, 13905, 13906, 13907, 13908, 13909, 13910, 13911, 13912, 13913, 13914, 13915, 13916, 13917, 14839, 14840, 14841}

def complete (a : Assignment) : Assignment := fun wire =>
  if wire = 728 then (a 98)⁻¹ else
  if wire = 729 then (a 10 + a 11)⁻¹ else
  if wire = 13904 then zeroFlag (1 - a 92) else
  if wire = 13905 then (1 - a 92)⁻¹ else
  if wire = 13906 then zeroFlag (1 - a 93) else
  if wire = 13907 then (1 - a 93)⁻¹ else
  if wire = 13908 then zeroFlag (2 - a 92) else
  if wire = 13909 then (2 - a 92)⁻¹ else
  if wire = 13910 then zeroFlag (2 - a 93) else
  if wire = 13911 then (2 - a 93)⁻¹ else
  if wire = 13912 then zeroFlag (a 94) else
  if wire = 13913 then (a 94)⁻¹ else
  if wire = 13914 then zeroFlag (a 95) else
  if wire = 13915 then (a 95)⁻¹ else
  if wire = 13916 then zeroFlag (a 96) else
  if wire = 13917 then (a 96)⁻¹ else
  if wire = 14839 then (a 97)⁻¹ else
  if wire = 14840 then (a 100 - a 99)⁻¹ else
  if wire = 14841 then (a 102 - a 101)⁻¹ else
  a wire

theorem complete_preserves (a : Assignment) (wire : ℕ) (h : wire ∉ writeSet) :
    complete a wire = a wire := by
  simp only [writeSet, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  simp_all [complete]

theorem writeSet_card : writeSet.card = 19 := by decide

/-- Every primary input and public/statement wire is below this boundary. -/
theorem complete_preserves_below (a : Assignment) (wire : ℕ) (h : wire < 728) :
    complete a wire = a wire := by
  apply complete_preserves
  simp only [writeSet, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Raw forms of the canonical non-hash conditions needed by this fragment. -/
structure Conditions (a : Assignment) : Prop where
  constant : a 0 = 1
  input0_range : (a 10).val < 2^128
  input1_range : (a 11).val < 2^128
  input_positive : 0 < (a 10).val + (a 11).val
  sink0 : (a 94 = 0 → a 92 = 1) ∧ (a 94 ≠ 0 → a 92 ≠ 1 ∧ a 92 ≠ 2)
  sink1 : (a 95 = 0 → a 93 = 2) ∧ (a 95 ≠ 0 → a 93 ≠ 1 ∧ a 93 ≠ 2)
  authorizer_positive : 0 < (a 98).val
  nullifiers_distinct : a 99 ≠ a 100
  outputs_distinct : a 101 ≠ a 102
  public_recipient : a 96 = 0 ↔ a 97 = 0

/-- Canonical R supplies all fragment conditions; no R1CS satisfaction is used. -/
theorem conditions_of_relation (a : Assignment) (hzero : a 0 = 1)
    (h : MSP.R (ConcreteWitness.statementOf a) (ConcreteWitness.ofAssignment a)) :
    Conditions a := by
  rcases h with ⟨_, _, _, _, _, _, hrange, _, hpos, hsink, hn, ho, _, ha, _, hpr⟩
  refine ⟨hzero, ?_, ?_, hpos, hsink 0, hsink 1, ha, hn, ho, hpr⟩
  · exact hrange ((ConcreteWitness.ofAssignment a).v 0) (by simp)
  · exact hrange ((ConcreteWitness.ofAssignment a).v 1) (by simp)

private theorem zero_complete (x : F) :
    x * x⁻¹ = 1 - zeroFlag x ∧ x * zeroFlag x = 0 := by
  by_cases h : x = 0 <;> simp [zeroFlag, h]

private theorem sink_complete (value inner target : F)
    (h : (value = 0 → inner = target) ∧ (value ≠ 0 → inner ≠ 1 ∧ inner ≠ 2)) :
    (inner - target) * zeroFlag value = 0 ∧
    (1 - zeroFlag value) * zeroFlag (1 - inner) = 0 ∧
    (1 - zeroFlag value) * zeroFlag (2 - inner) = 0 := by
  by_cases hz : value = 0
  · simp [zeroFlag, hz, h.1 hz]
  · have h1 : 1 - inner ≠ 0 := sub_ne_zero.mpr (h.2 hz).1.symm
    have h2 : 2 - inner ≠ 0 := sub_ne_zero.mpr (h.2 hz).2.symm
    simp [zeroFlag, hz, h1, h2]

def c634 : Constraint := ⟨[(98, 1)], [(728, 1)], [(0, 1)]⟩

def c13868 : Constraint := ⟨[(96, 1)], [(13917, 1)], [(0, 1), (13916, 21888242871839275222246405745257275088548364400416034343698204186575808495616)]⟩

def c13869 : Constraint := ⟨[(96, 1)], [(13916, 1)], []⟩

def c14798 : Constraint := ⟨[(97, 1)], [(14839, 1)], [(0, 1), (13916, 21888242871839275222246405745257275088548364400416034343698204186575808495616)]⟩

def c14799 : Constraint := ⟨[(97, 1)], [(13916, 1)], []⟩

def c14800 : Constraint := ⟨[(99, 21888242871839275222246405745257275088548364400416034343698204186575808495616), (100, 1)], [(14840, 1)], [(0, 1)]⟩

def c14801 : Constraint := ⟨[(101, 21888242871839275222246405745257275088548364400416034343698204186575808495616), (102, 1)], [(14841, 1)], [(0, 1)]⟩

def basic : List Constraint :=
  [c634, InputNonzero.constraint, c13868, c13869, c14798, c14799, c14800, c14801]

/-- The additional eight controls are literal slices of the pinned R1CS. -/
theorem basic_eq_slices : basic =
    (Spend.group2.drop 122).take 2 ++ (Spend.group54.drop 44).take 2 ++
      (Spend.group57.drop 206).take 4 := rfl

def constraints : List Constraint := controls ++ gadgets ++ basic

theorem constraints_length : constraints.length = 26 := rfl

theorem constraints_mem {c : Constraint} (hc : c ∈ constraints) :
    c ∈ Spend.system.constraints := by
  simp only [constraints, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · rw [SinkGates.controls_eq_slice] at hc
    exact List.mem_flatten.mpr
      ⟨Spend.group1, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
  · rw [SinkGates.gadgets_eq_slice] at hc
    exact List.mem_flatten.mpr
      ⟨Spend.group54, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
  · rw [basic_eq_slices] at hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact List.mem_flatten.mpr
        ⟨Spend.group2, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
    · exact List.mem_flatten.mpr
        ⟨Spend.group54, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
    · exact List.mem_flatten.mpr
        ⟨Spend.group57, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

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

theorem gadgets_complete (a : Assignment) (h : Conditions a) :
    ∀ c ∈ gadgets, c.Holds (complete a) := by
  have h1 := zero_complete (1 - a 92)
  have h2 := zero_complete (1 - a 93)
  have h3 := zero_complete (2 - a 92)
  have h4 := zero_complete (2 - a 93)
  have h5 := zero_complete (a 94)
  have h6 := zero_complete (a 95)
  simp only [sub_eq_add_neg] at h1 h2 h3 h4 h5 h6
  simp [-mul_eq_zero, gadgets, c13856, c13857, c13858, c13859, c13860, c13861, c13862, c13863, c13864, c13865, c13866, c13867, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, sub_eq_add_neg]
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2⟩

theorem controls_complete (a : Assignment) (h : Conditions a) :
    ∀ c ∈ controls, c.Holds (complete a) := by
  have h0 := sink_complete (a 94) (a 92) 1 h.sink0
  have h1 := sink_complete (a 95) (a 93) 2 h.sink1
  simp only [sub_eq_add_neg] at h0 h1
  simp [-mul_eq_zero, controls, c468, c469, c470, c471, c472, c473, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg]
  exact ⟨by linear_combination h0.1, h0.2.1, h0.2.2,
    by linear_combination h1.1, h1.2.1, h1.2.2⟩

theorem basic_complete (a : Assignment) (h : Conditions a) :
    ∀ c ∈ basic, c.Holds (complete a) := by
  have ha : a 98 ≠ 0 := by
    intro hz
    have hp := h.authorizer_positive
    simp [hz] at hp
  have hn : a 100 - a 99 ≠ 0 := sub_ne_zero.mpr h.nullifiers_distinct.symm
  have ho : a 102 - a 101 ≠ 0 := sub_ne_zero.mpr h.outputs_distinct.symm
  have hp := zero_complete (a 96)
  have hr := zero_complete (a 97)
  have hf : zeroFlag (a 97) = zeroFlag (a 96) := by
    simp only [zeroFlag, h.public_recipient]
  rw [hf] at hr
  have hi := InputCompleteness.input_gate_complete (complete a)
    (by simpa [complete] using h.constant)
    (by simpa [complete] using h.input0_range)
    (by simpa [complete] using h.input1_range)
    (by simpa [complete] using h.input_positive) (by simp [complete])
  simp only [basic, List.mem_cons, forall_eq_or_imp]
  refine ⟨?_, hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c634, Constraint.Holds, LinearCombination.eval, complete, h.constant, ha]
  · simpa [c13868, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg] using hp.1
  · simpa [c13869, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg] using hp.2
  · simpa [c14798, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg] using hr.1
  · simpa [c14799, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg] using hr.2
  · simpa [c14800, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg, add_comm] using mul_inv_cancel₀ hn
  · simpa [c14801, Constraint.Holds, LinearCombination.eval, complete, h.constant, neg_one, neg_two, sub_eq_add_neg, add_comm] using mul_inv_cancel₀ ho

/-- All 26 pinned control constraints hold after filling only the 19 auxiliaries. -/
theorem complete_holds (a : Assignment) (h : Conditions a) :
    ∀ c ∈ constraints, c.Holds (complete a) := by
  intro c hc
  simp only [constraints, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact controls_complete a h c hc
  · exact gadgets_complete a h c hc
  · exact basic_complete a h c hc

/-- Relation-level entry point for assembling a complete circuit assignment. -/
theorem complete_holds_of_relation (a : Assignment) (hzero : a 0 = 1)
    (h : MSP.R (ConcreteWitness.statementOf a) (ConcreteWitness.ofAssignment a)) :
    ∀ c ∈ constraints, c.Holds (complete a) :=
  complete_holds a (conditions_of_relation a hzero h)

#print axioms complete_preserves
#print axioms constraints_mem
#print axioms complete_holds
#print axioms complete_holds_of_relation

end MSP.Artifacts.ControlCompleteness
