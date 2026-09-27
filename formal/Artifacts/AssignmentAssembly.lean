import Artifacts.R1CS
import Mathlib.Data.Fin.Basic

/-! Combine independently constructed circuit fragments. Their physical write
sets are disjoint, and all shared boundary values agree with one seed. Thus
local constraint proofs survive composition without a circular satisfaction
hypothesis or a trusted witness generator. -/
namespace MSP.Artifacts.AssignmentAssembly

structure Part where
  writes : ℕ → Prop
  assignment : Assignment
  constraints : List Constraint

def Supported (localWires boundary : ℕ → Prop) (c : Constraint) : Prop :=
  ∀ term ∈ c.a ++ c.b ++ c.c, localWires term.1 ∨ boundary term.1

noncomputable def merge {n : ℕ} (parts : Fin n → Part) (seed : Assignment) : Assignment := by
  classical
  exact fun wire => if h : ∃ i, (parts i).writes wire then
    (parts h.choose).assignment wire else seed wire

variable {n : ℕ} (parts : Fin n → Part) (seed : Assignment)

/-- Exclusive ownership of a written wire. -/
def Exclusive : Prop := ∀ i j wire, (parts i).writes wire → (parts j).writes wire → i = j

theorem merge_written (exclusive : Exclusive parts) (i : Fin n) (wire : ℕ)
    (h : (parts i).writes wire) : merge parts seed wire = (parts i).assignment wire := by
  unfold merge
  split
  next hx =>
    have he : hx.choose = i := exclusive hx.choose i wire hx.choose_spec h
    rw [he]
  next hx => exact False.elim (hx ⟨i,h⟩)

theorem merge_unwritten (wire : ℕ) (h : ∀ i, ¬ (parts i).writes wire) :
    merge parts seed wire = seed wire := by
  unfold merge
  rw [dite_eq_right (by simpa only [not_exists] using h)]

theorem merge_boundary (boundary : ℕ → Prop)
    (agrees : ∀ i wire, boundary wire → (parts i).assignment wire = seed wire)
    (wire : ℕ) (h : boundary wire) : merge parts seed wire = seed wire := by
  unfold merge
  split
  · exact agrees _ wire h
  · rfl

private theorem eval_congr (form : LinearCombination) (a b : Assignment)
    (h : ∀ term ∈ form, a term.1 = b term.1) : form.eval a = form.eval b := by
  unfold LinearCombination.eval
  congr 1
  apply List.map_congr_left
  intro term ht
  rw [h term ht]

/-- A constraint depends only on the wire values appearing in its coefficients. -/
theorem holds_congr (c : Constraint) (a b : Assignment)
    (h : ∀ term ∈ c.a ++ c.b ++ c.c, a term.1 = b term.1) :
    c.Holds a ↔ c.Holds b := by
  have ha := eval_congr c.a a b (fun t ht => h t (by simp [ht]))
  have hb := eval_congr c.b a b (fun t ht => h t (by simp [ht]))
  have hc := eval_congr c.c a b (fun t ht => h t (by simp [ht]))
  simp only [Constraint.Holds, ha, hb, hc]

/-- Each local constraint remains true in the combined assignment. -/
theorem merge_holds (boundary : ℕ → Prop) (exclusive : Exclusive parts)
    (agrees : ∀ i wire, boundary wire → (parts i).assignment wire = seed wire)
    (supported : ∀ i c, c ∈ (parts i).constraints → Supported (parts i).writes boundary c)
    (localHolds : ∀ i c, c ∈ (parts i).constraints → c.Holds (parts i).assignment)
    (i : Fin n) (c : Constraint) (hc : c ∈ (parts i).constraints) :
    c.Holds (merge parts seed) := by
  apply (holds_congr c (merge parts seed) (parts i).assignment ?_).mpr (localHolds i c hc)
  intro term ht
  rcases supported i c hc term ht with hw | hb
  · exact merge_written parts seed exclusive i term.1 hw
  · exact (merge_boundary parts seed boundary agrees term.1 hb).trans (agrees i term.1 hb).symm

/-- End-to-end constraint assembly, conditional only on the explicitly supplied
local proofs and finite write/read/coverage certificates. -/
theorem satisfied (system : System) (boundary : ℕ → Prop)
    (exclusive : Exclusive parts) (hzero : seed 0 = 1) (zeroBoundary : boundary 0)
    (agrees : ∀ i wire, boundary wire → (parts i).assignment wire = seed wire)
    (supported : ∀ i c, c ∈ (parts i).constraints → Supported (parts i).writes boundary c)
    (localHolds : ∀ i c, c ∈ (parts i).constraints → c.Holds (parts i).assignment)
    (coverage : ∀ c ∈ system.constraints, ∃ i, c ∈ (parts i).constraints) :
    system.Satisfied (merge parts seed) := by
  constructor
  · exact (merge_boundary parts seed boundary agrees 0 zeroBoundary).trans hzero
  · intro c hc
    obtain ⟨i, hi⟩ := coverage c hc
    exact merge_holds parts seed boundary exclusive agrees supported localHolds i c hi

#print axioms satisfied
end MSP.Artifacts.AssignmentAssembly
