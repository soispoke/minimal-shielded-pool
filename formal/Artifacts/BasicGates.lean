import Artifacts.InputNonzero
import Artifacts.Compression

/-! Actual inverse and IsZero gates of the pinned R1CS.
Each literal constraint is checked for membership in the complete generated system.
These prove relation fragments without assuming the high-level relation. -/

namespace MSP.Artifacts.BasicGates

private def c634 : Constraint := ⟨[(98, 1)], [(728, 1)], [(0, 1)]⟩

private theorem c634_mem : c634 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group2, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk79, by simp, by simp [Spend.chunk79, c634]⟩

private def c13868 : Constraint := ⟨[(96, 1)], [(13917, 1)], [(0, 1), (13916, 21888242871839275222246405745257275088548364400416034343698204186575808495616)]⟩

private theorem c13868_mem : c13868 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group54, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk1733, by simp, by simp [Spend.chunk1733, c13868]⟩

private def c13869 : Constraint := ⟨[(96, 1)], [(13916, 1)], []⟩

private theorem c13869_mem : c13869 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group54, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk1733, by simp, by simp [Spend.chunk1733, c13869]⟩

private def c14798 : Constraint := ⟨[(97, 1)], [(14839, 1)], [(0, 1), (13916, 21888242871839275222246405745257275088548364400416034343698204186575808495616)]⟩

private theorem c14798_mem : c14798 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group57, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk1849, by simp, by simp [Spend.chunk1849, c14798]⟩

private def c14799 : Constraint := ⟨[(97, 1)], [(13916, 1)], []⟩

private theorem c14799_mem : c14799 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group57, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk1849, by simp, by simp [Spend.chunk1849, c14799]⟩

private def c14800 : Constraint := ⟨[(99, 21888242871839275222246405745257275088548364400416034343698204186575808495616), (100, 1)], [(14840, 1)], [(0, 1)]⟩

private theorem c14800_mem : c14800 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group57, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk1850, by simp, by simp [Spend.chunk1850, c14800]⟩

private def c14801 : Constraint := ⟨[(101, 21888242871839275222246405745257275088548364400416034343698204186575808495616), (102, 1)], [(14841, 1)], [(0, 1)]⟩

private theorem c14801_mem : c14801 ∈ Spend.system.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group57, by simp, ?_⟩
  apply List.mem_flatten.mpr
  exact ⟨Spend.chunk1850, by simp, by simp [Spend.chunk1850, c14801]⟩

private theorem neg_one :
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 : F) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  norm_num
  exact ZMod.natCast_self p

theorem authorizer_ne_zero (w : Assignment) (h : Spend.system.Satisfied w) :
    w 98 ≠ 0 := by
  have hc := h.2 _ c634_mem
  simp [c634, Constraint.Holds, LinearCombination.eval, h.1] at hc
  intro hz
  simp [hz] at hc

theorem authorizer_positive (w : Assignment) (h : Spend.system.Satisfied w) :
    0 < (w 98).val := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact authorizer_ne_zero w h ((ZMod.val_eq_zero _).mp hz)

theorem nullifiers_distinct (w : Assignment) (h : Spend.system.Satisfied w) :
    w 99 ≠ w 100 := by
  have hc := h.2 _ c14800_mem
  simp [c14800, Constraint.Holds, LinearCombination.eval, h.1, neg_one] at hc
  intro hz
  rw [← hz] at hc
  simp at hc

theorem outputs_distinct (w : Assignment) (h : Spend.system.Satisfied w) :
    w 101 ≠ w 102 := by
  have hc := h.2 _ c14801_mem
  simp [c14801, Constraint.Holds, LinearCombination.eval, h.1, neg_one] at hc
  intro hz
  rw [← hz] at hc
  simp at hc

/-- Both IsZero gadgets share the actual output wire 13916. -/
theorem public_zero_iff_recipient_zero (w : Assignment)
    (h : Spend.system.Satisfied w) : w 96 = 0 ↔ w 97 = 0 := by
  have hp := h.2 _ c13868_mem
  have hp0 := h.2 _ c13869_mem
  have hr := h.2 _ c14798_mem
  have hr0 := h.2 _ c14799_mem
  simp [c13868, c13869, c14798, c14799, Constraint.Holds,
    LinearCombination.eval, h.1, neg_one] at hp hp0 hr hr0
  have hp' := (MSP.isZero_sound (w 96) (w 13917) (w 13916)
    (by linear_combination hp) (mul_eq_zero.mpr hp0)).1
  have hr' := (MSP.isZero_sound (w 97) (w 14839) (w 13916)
    (by linear_combination hr) (mul_eq_zero.mpr hr0)).1
  exact hp'.symm.trans hr'

/-- R8 and the non-range part of R9 for the compression statement projection. -/
theorem statement_checks (w : Assignment) (h : Spend.system.Satisfied w) :
    let x := Compression.statement w
    x.nf1 ≠ x.nf2 ∧ x.o1 ≠ x.o2 ∧ 0 < x.auth.val ∧ (x.pub = 0 ↔ x.rcp = 0) :=
  ⟨nullifiers_distinct w h, outputs_distinct w h, authorizer_positive w h,
    public_zero_iff_recipient_zero w h⟩

#print axioms statement_checks

end MSP.Artifacts.BasicGates
