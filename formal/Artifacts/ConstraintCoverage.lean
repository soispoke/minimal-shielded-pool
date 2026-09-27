import Artifacts.ConstraintCoverageData

/-! Reverse coverage and the full-system assembly rule. Every actual constraint
belongs to a proved fragment, as established by the ordered kernel certificates.
Satisfaction of those fragments is the only remaining assembly premise. -/

namespace MSP.Artifacts.ConstraintCoverage

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Reverse coverage of the entire pinned R1CS, with no coverage hypothesis. -/
theorem covers {c : Constraint} (hc : c ∈ Spend.system.constraints) :
    ∃ family : Family, c ∈ family.constraints := by
  rw [ordered_eq] at hc
  obtain ⟨block, hb, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨pieces, _, rfl⟩ := List.mem_map.mp hb
  exact expand_covered hc

/-- An assignment satisfying every named fragment satisfies the full R1CS. -/
theorem satisfied_of_families (a : Assignment) (hzero : a 0 = 1)
    (h : ∀ family : Family, ∀ c ∈ family.constraints, c.Holds a) :
    Spend.system.Satisfied a := by
  refine ⟨hzero, ?_⟩
  intro c hc
  obtain ⟨family, hf⟩ := covers hc
  exact h family c hf

/-- The concrete assembly interface uses the existing fragment theorem lists. -/
theorem satisfied_of_fragments (a : Assignment) (hzero : a 0 = 1)
    (hgamma : ∀ c ∈ CompressionData.constraints, c.Holds a)
    (hbeta : ∀ c ∈ BetaGatesData.constraints, c.Holds a)
    (hsmall : ∀ i : Fin 54, ∀ c ∈ (SmallHashGatesData.gate i).constraints, c.Holds a)
    (hranges : ∀ c ∈ RangeAssignmentCompleteness.constraints, c.Holds a)
    (hcontrols : ∀ c ∈ ControlCompleteness.constraints, c.Holds a)
    (hpaths : ∀ c ∈ PathCompleteness.constraints, c.Holds a) :
    Spend.system.Satisfied a := by
  apply satisfied_of_families a hzero
  intro family
  cases family with
  | gamma => exact hgamma
  | beta => exact hbeta
  | small i => exact hsmall i
  | ranges => exact hranges
  | controls => exact hcontrols
  | paths => exact hpaths

/-- Small-hash counts are obtained from their typed, checked constraint counts. -/
theorem small_count :
    ((List.finRange 54).flatMap fun i => (SmallHashGatesData.gate i).constraints).length = 13098 := by
  simp only [List.length_flatMap, SmallHashGates.Instance.constraintCount]
  rfl

theorem family_counts :
    CompressionData.constraints.length = 9 ∧ BetaGatesData.constraints.length = 459 ∧
    RangeAssignmentCompleteness.constraints.length = 1088 ∧
    ControlCompleteness.constraints.length = 26 ∧ PathCompleteness.constraints.length = 122 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms ordered_eq
#print axioms covers
#print axioms satisfied_of_fragments
#print axioms small_count
#print axioms family_counts

end MSP.Artifacts.ConstraintCoverage
