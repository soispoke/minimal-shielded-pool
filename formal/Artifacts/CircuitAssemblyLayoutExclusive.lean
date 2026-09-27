import Artifacts.CircuitAssemblyLayout

/-! Finite interval certificates for exclusive ownership and boundary outputs. -/
namespace MSP.Artifacts.CircuitAssemblyLayout

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Compare only the compact intervals, rather than pairs of all physical wires. -/
theorem interval_separation : ∀ i j : Fin 59, i ≠ j →
    ∀ x ∈ spans i, ∀ y ∈ spans j, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

theorem exclusive (i j : Fin 59) (wire : ℕ) (hi : writes i wire) (hj : writes j wire) :
    i = j := by
  by_contra hij
  obtain ⟨x, hx, hxi, hxj⟩ := hi
  obtain ⟨y, hy, hyi, hyj⟩ := hj
  have hs := interval_separation i j hij x hx y hy
  omega

theorem output_owned : ∀ i : Fin 55,
    writes ⟨i.val, by omega⟩ (outputWire i) ∧ boundary (outputWire i) := by decide

private def boundarySpans : List (ℕ × ℕ) :=
  [(0, 103), (730, 792), (7060, 7122), (1031, 1033), (7361, 7363), (6309, 6310), (12639, 12640)]

private theorem boundary_span (wire : ℕ) :
    boundary wire ↔ ∃ s ∈ boundarySpans, s.1 ≤ wire ∧ wire < s.2 := by
  simp [boundary, boundarySpans]
  omega

private theorem boundary_intersection : ∀ i : Fin 55,
    ∀ s ∈ spans ⟨i.val, by omega⟩, ∀ b ∈ boundarySpans,
      (s.2 ≤ b.1 ∨ b.2 ≤ s.1) ∨
      (max s.1 b.1 = outputWire i ∧ min s.2 b.2 = outputWire i + 1) := by decide

/-- A hash component writes only its final output on the shared boundary. -/
theorem hash_boundary (i : Fin 55) (wire : ℕ)
    (hw : writes ⟨i.val, by omega⟩ wire) (hb : boundary wire) : wire = outputWire i := by
  obtain ⟨s, hs, hl, hu⟩ := hw
  obtain ⟨b, hb, hbl, hbu⟩ := (boundary_span wire).mp hb
  have he := boundary_intersection i s hs b hb
  omega

theorem hash_boundary_iff (i : Fin 55) (wire : ℕ) :
    writes ⟨i.val, by omega⟩ wire ∧ boundary wire ↔ wire = outputWire i := by
  constructor
  · intro h
    exact hash_boundary i wire h.1 h.2
  · rintro rfl
    exact output_owned i

private theorem nonhash_separation : ∀ i : Fin 59, 55 ≤ i.val →
    ∀ s ∈ spans i, ∀ b ∈ boundarySpans, s.2 ≤ b.1 ∨ b.2 ≤ s.1 := by decide

theorem nonhash_boundary (i : Fin 59) (hi : 55 ≤ i.val) (wire : ℕ)
    (hb : boundary wire) : ¬ writes i wire := by
  rintro ⟨s, hs, hl, hu⟩
  obtain ⟨b, hb, hbl, hbu⟩ := (boundary_span wire).mp hb
  have he := nonhash_separation i hi s hs b hb
  omega

#print axioms exclusive
#print axioms hash_boundary_iff
#print axioms nonhash_boundary

end MSP.Artifacts.CircuitAssemblyLayout
