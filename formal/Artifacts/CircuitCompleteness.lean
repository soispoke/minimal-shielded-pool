import Spec.Circuit
import Artifacts.SemanticAssignmentBoundary
import Artifacts.CircuitAssemblyLayoutSupport
import Artifacts.CircuitAssemblyLayoutBindings
import Artifacts.CircuitAssemblyLayoutExclusive
import Artifacts.HashAssignmentCompletenessBeta
import Artifacts.RangeAssignmentCompletenessRelation

/-! A complete physical witness for every canonical valid spend. Independent
hash, range, control, compression and path fragments share a proved semantic
boundary and disjoint write sets. Exact ordered coverage closes all 14,802
constraints, and source agreement preserves every required projection. -/
namespace MSP.Artifacts.CircuitCompleteness

open CircuitAssemblyLayout
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

noncomputable def localAssignment (seed : Assignment) (i : Fin 59) : Assignment :=
  if h : i.val = 0 then HashAssignmentCompletenessBeta.complete seed
  else if h : i.val < 55 then
    HashAssignmentCompletenessSmall.assignment ⟨i.val - 1, by omega⟩ seed
  else if i.val = 55 then RangeAssignmentCompleteness.complete seed
  else if i.val = 56 then ControlCompleteness.complete seed
  else if i.val = 57 then GammaCompleteness.complete seed
  else seed

theorem local_small (seed : Assignment) (i : Fin 54) :
    localAssignment seed (smallPart i) = HashAssignmentCompletenessSmall.assignment i seed := by
  simp only [localAssignment, smallPart, show i.val+1 ≠ 0 by omega,
    ↓reduceDIte, show i.val+1 < 55 by omega, Nat.add_sub_cancel]

private theorem all_parts (P : Fin 59 → Prop)
    (hbeta : P 0) (hsmall : ∀ i, P (smallPart i))
    (hrange : P 55) (hcontrol : P 56) (hgamma : P 57) (hpath : P 58) : ∀ i, P i := by
  intro i
  by_cases hz : i.val = 0
  · have he : i = 0 := Fin.ext hz
    simpa only [he] using hbeta
  by_cases hs : i.val < 55
  · let j : Fin 54 := ⟨i.val-1, by omega⟩
    have he : smallPart j = i := by apply Fin.ext; dsimp [smallPart,j]; omega
    simpa only [he] using hsmall j
  have hc : i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 := by
    have hb := i.isLt
    have hval : i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 := by omega
    rcases hval with he|he|he|he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Or.inl (Fin.ext he))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext he)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext he)))
  rcases hc with rfl|rfl|rfl|rfl
  · exact hrange
  · exact hcontrol
  · exact hgamma
  · exact hpath

noncomputable def part (seed : Assignment) (i : Fin 59) : AssignmentAssembly.Part where
  writes := writes i
  assignment := localAssignment seed i
  constraints := constraints i

private theorem seed_relation (x : Statement) (w : MSP.Witness) (al : F) (h : R x w) :
    R (ConcreteWitness.statementOf (SemanticAssignment.build x w al))
      (ConcreteWitness.ofAssignment (SemanticAssignment.build x w al)) := by
  obtain ⟨hs,hw,_⟩ := SemanticAssignment.projections x w al h
  rw [hs,hw]
  exact h

private theorem seed_beta (x : Statement) (w : MSP.Witness) (al : F) :
    SemanticAssignment.build x w al 1 = β x :=
  (SemanticAssignment.source_agreement x w al 1 (by decide)).trans rfl

private theorem seed_gamma (x : Statement) (w : MSP.Witness) (al : F) (h : R x w) :
    SemanticAssignment.build x w al 2 =
      γ (Compression.statement (SemanticAssignment.build x w al))
        (SemanticAssignment.build x w al 3 + SemanticAssignment.build x w al 1) := by
  have hs := (SemanticAssignment.projections x w al h).1
  change Compression.statement (SemanticAssignment.build x w al) = x at hs
  rw [hs, seed_beta, SemanticAssignment.source_agreement x w al 2 (by decide),
    SemanticAssignment.source_agreement x w al 3 (by decide)]
  rfl

theorem local_holds (x : Statement) (w : MSP.Witness) (al : F) (h : R x w) :
    ∀ i c, c ∈ constraints i → c.Holds (localAssignment (SemanticAssignment.build x w al) i) := by
  let seed := SemanticAssignment.build x w al
  have hz : seed 0 = 1 := SemanticAssignment.constant x w al
  apply all_parts
  · exact HashAssignmentCompletenessBeta.complete_holds seed hz
  · intro i
    rw [constraints_small, local_small]
    exact (HashAssignmentCompletenessSmall.complete i seed hz).1
  · exact RangeAssignmentCompleteness.complete_holds_of_relation seed hz (seed_relation x w al h)
  · exact ControlCompleteness.complete_holds_of_relation seed hz (seed_relation x w al h)
  · exact GammaCompleteness.complete_holds seed (seed_gamma x w al h)
  · exact (SemanticAssignment.path_complete x w al h).2.1

private theorem beta_boundary (x : Statement) (w : MSP.Witness) (al : F) (h : R x w)
    (wire : ℕ) (hb : boundary wire) :
    HashAssignmentCompletenessBeta.complete (SemanticAssignment.build x w al) wire =
      SemanticAssignment.build x w al wire := by
  by_cases hw : wire = 1
  · subst wire
    rw [HashAssignmentCompletenessBeta.complete_beta _ (SemanticAssignment.constant x w al), seed_beta]
    have hs := (SemanticAssignment.projections x w al h).1
    change Compression.statement (SemanticAssignment.build x w al) = x at hs
    rw [hs]
  · apply HashAssignmentCompletenessBeta.complete_preserves
    constructor
    · exact hw
    · unfold boundary at hb
      omega

private theorem range_boundary (seed : Assignment) (wire : ℕ) (hb : boundary wire) :
    RangeAssignmentCompleteness.complete seed wire = seed wire := by
  apply RangeAssignmentCompleteness.preserves
  exact (range_writes wire).not.mp (nonhash_boundary 55 (by decide) wire hb)

private theorem control_boundary (seed : Assignment) (wire : ℕ) (hb : boundary wire) :
    ControlCompleteness.complete seed wire = seed wire := by
  apply ControlCompleteness.complete_preserves
  exact (control_writes wire).not.mp (nonhash_boundary 56 (by decide) wire hb)

private theorem gamma_boundary (seed : Assignment) (wire : ℕ) (hb : boundary wire) :
    GammaCompleteness.complete seed wire = seed wire := by
  apply GammaCompleteness.complete_preserves
  exact (gamma_writes wire).not.mp (nonhash_boundary 57 (by decide) wire hb)

-- All concrete boundary agreements are proved before the assignments are merged.
theorem boundary_agreement (x : Statement) (w : MSP.Witness) (al : F) (h : R x w) :
    ∀ i wire, boundary wire →
      localAssignment (SemanticAssignment.build x w al) i wire = SemanticAssignment.build x w al wire := by
  apply all_parts
  · exact beta_boundary x w al h
  · intro i
    rw [local_small]
    exact SemanticAssignment.small_boundary x w al h i
  · exact range_boundary _
  · exact control_boundary _
  · exact gamma_boundary _
  · intro wire hb
    rfl

noncomputable def assignment (x : Statement) (w : MSP.Witness) (al : F) : Assignment :=
  let seed := SemanticAssignment.build x w al
  AssignmentAssembly.merge (part seed) seed

theorem assignment_satisfied (x : Statement) (w : MSP.Witness) (al : F) (h : R x w) :
    Spend.system.Satisfied (assignment x w al) := by
  apply AssignmentAssembly.satisfied (part (SemanticAssignment.build x w al))
    (SemanticAssignment.build x w al) Spend.system boundary
  · exact exclusive
  · exact SemanticAssignment.constant x w al
  · exact source_boundary 0 (by decide)
  · exact boundary_agreement x w al h
  · exact supported
  · exact local_holds x w al h
  · intro c hc
    exact coverage hc

theorem assignment_source (x : Statement) (w : MSP.Witness) (al : F) (h : R x w)
    (wire : ℕ) (hw : wire < 103) :
    assignment x w al wire = BaseAssignment.build x w al wire := by
  have he := AssignmentAssembly.merge_boundary (part (SemanticAssignment.build x w al))
    (SemanticAssignment.build x w al) boundary (boundary_agreement x w al h)
    wire (source_boundary wire hw)
  exact he.trans (SemanticAssignment.source_agreement x w al wire hw)

theorem assignment_projections (x : Statement) (w : MSP.Witness) (al : F) (h : R x w) :
    ConcreteWitness.statementOf (assignment x w al) = x ∧
    ConcreteWitness.ofAssignment (assignment x w al) = w ∧
    ConcreteWitness.publicOf (assignment x w al) = (β x, γ x (al+β x), al) :=
  BaseAssignment.projections_of_agreement _ x w al h (assignment_source x w al h)

end MSP.Artifacts.CircuitCompleteness

namespace MSP
/-- C1c for the actual pinned constraint system and concrete projections. -/
theorem c1c : C1c := by
  intro x w al h
  refine ⟨Artifacts.CircuitCompleteness.assignment x w al, ?_, ?_⟩
  · unfold Satisfied
    exact Artifacts.CircuitCompleteness.assignment_satisfied x w al h
  · unfold stmtOf witOf publicOf
    exact Artifacts.CircuitCompleteness.assignment_projections x w al h
#print axioms c1c
end MSP
