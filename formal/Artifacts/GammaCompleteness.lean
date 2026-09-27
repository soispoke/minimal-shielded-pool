import Artifacts.BaseAssignment

/-! Fill the eight retained Horner intermediates, wires 103 through 110,
while keeping the public gamma output fixed. All nine actual prefix constraints
then follow from its canonical polynomial value. -/

namespace MSP.Artifacts.GammaCompleteness

open CompressionData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Accumulate the statement coefficients from highest degree to lowest. -/
def horner (x : Statement) (s : F) (n : ℕ) : F :=
  ([x.rcp, x.fee, x.pub, x.d, x.root, x.o2, x.o1, x.nf2, x.nf1].take n).foldl
    (fun acc coeff => acc * s + coeff) x.auth

theorem horner_gamma (x : Statement) (s : F) : horner x s 9 = γ x s := by
  simp [horner, γ, Statement.vec, Fin.sum_univ_succ]
  ring

def writeSet : Finset ℕ := Finset.Ico 103 111

theorem writeSet_card : writeSet.card = 8 := by decide

def complete (a : Assignment) : Assignment := fun wire =>
  if wire = 110 then horner (Compression.statement a) (a 3 + a 1) 1 else
  if wire = 109 then horner (Compression.statement a) (a 3 + a 1) 2 else
  if wire = 108 then horner (Compression.statement a) (a 3 + a 1) 3 else
  if wire = 107 then horner (Compression.statement a) (a 3 + a 1) 4 else
  if wire = 106 then horner (Compression.statement a) (a 3 + a 1) 5 else
  if wire = 105 then horner (Compression.statement a) (a 3 + a 1) 6 else
  if wire = 104 then horner (Compression.statement a) (a 3 + a 1) 7 else
  if wire = 103 then horner (Compression.statement a) (a 3 + a 1) 8 else
  a wire

theorem complete_preserves (a : Assignment) (wire : ℕ) (h : wire ∉ writeSet) :
    complete a wire = a wire := by
  simp only [writeSet, Finset.mem_Ico] at h
  simp only [complete]
  split_ifs <;> first | omega | rfl

theorem complete_preserves_sources (a : Assignment) (wire : ℕ) (h : wire < 103) :
    complete a wire = a wire := by
  apply complete_preserves
  simp only [writeSet, Finset.mem_Ico]
  omega

private theorem neg_one :
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 : F) = -1 :=
  RangeGate.coefficient_neg_one

/-- Actual constraints 0 through 8 hold after filling the intermediates.
The premise is the canonical public gamma value, not a constraint premise. -/
theorem complete_holds (a : Assignment)
    (hgamma : a 2 = γ (Compression.statement a) (a 3 + a 1)) :
    ∀ c ∈ CompressionData.constraints, c.Holds (complete a) := by
  simp only [constraints, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    forall_false]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, Constraint.Holds,
      LinearCombination.eval, complete, neg_one, horner, hgamma,
      Compression.statement, γ, Statement.vec, Fin.sum_univ_succ] <;> ring_nf
  simp

/-- Completing the canonical base needs no additional premises beyond R. -/
theorem base_complete_holds (x : Statement) (w : MSP.Witness) (al : F)
    (h : MSP.R x w) :
    ∀ c ∈ CompressionData.constraints, c.Holds (complete (BaseAssignment.build x w al)) := by
  apply complete_holds
  have hs := BaseAssignment.statementOf x w al h
  change Compression.statement (BaseAssignment.build x w al) = x at hs
  rw [hs]
  rfl

/-- Horner construction preserves all three concrete source projections. -/
theorem preserves_projections (a : Assignment) :
    ConcreteWitness.statementOf (complete a) = ConcreteWitness.statementOf a ∧
    ConcreteWitness.ofAssignment (complete a) = ConcreteWitness.ofAssignment a ∧
    ConcreteWitness.publicOf (complete a) = ConcreteWitness.publicOf a :=
  ⟨BaseAssignment.statementOf_congr _ _ (complete_preserves_sources a),
    BaseAssignment.ofAssignment_congr _ _ (complete_preserves_sources a),
    BaseAssignment.publicOf_congr _ _ (complete_preserves_sources a)⟩

#print axioms complete_holds
#print axioms base_complete_holds
#print axioms preserves_projections

end MSP.Artifacts.GammaCompleteness
