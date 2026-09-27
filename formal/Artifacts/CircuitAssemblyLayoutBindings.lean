import Artifacts.CircuitAssemblyLayoutExclusive
import Artifacts.HashAssignmentCompletenessSmall
import Artifacts.HashAssignmentCompletenessBetaData
import Artifacts.GammaCompleteness
import Mathlib.Data.List.Sort

/-! Exact binding of the compact write intervals to the real recovery plans and
power-wire layouts. Sorting is only a certificate format; membership is proved
for the original unsorted component lists. -/

namespace MSP.Artifacts.CircuitAssemblyLayout

open HashAssignmentCompleteness

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def spanWires (ss : List (ℕ × ℕ)) : List ℕ :=
  ss.flatMap fun s => List.range' s.1 (s.2 - s.1)

theorem mem_spanWires (i : Fin 59) (wire : ℕ) : wire ∈ spanWires (spans i) ↔ writes i wire := by
  simp only [spanWires, List.mem_flatMap, List.mem_range'_1, writes]
  constructor
  · rintro ⟨s, hs, hl, hu⟩
    exact ⟨s, hs, hl, by omega⟩
  · rintro ⟨s, hs, hl, hu⟩
    exact ⟨s, hs, hl, by omega⟩

def powerWires {g : SmallHashGates.Instance} (layout : PowerLayout g) : List ℕ :=
  ((List.finRange g.tripleCount).product (List.finRange 2)).map layout.wire

theorem mem_powerWires {g : SmallHashGates.Instance} (layout : PowerLayout g) (wire : ℕ) :
    wire ∈ powerWires layout ↔ ∃ k, layout.wire k = wire := by
  simp [powerWires]

private theorem sorted_membership (xs : List ℕ) (i : Fin 59)
    (h : xs.insertionSort (fun x y => x ≤ y) = spanWires (spans i)) (wire : ℕ) :
    writes i wire ↔ wire ∈ xs := by
  rw [← mem_spanWires, ← h, List.mem_insertionSort]

private theorem sorted0 :
    ((HashAssignmentCompletenessSmall.kit0).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit0).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 1) := by decide

private theorem sorted1 :
    ((HashAssignmentCompletenessSmall.kit1).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit1).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 2) := by decide

private theorem sorted2 :
    ((HashAssignmentCompletenessSmall.kit2).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit2).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 3) := by decide

private theorem sorted3 :
    ((HashAssignmentCompletenessSmall.kit3).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit3).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 4) := by decide

private theorem sorted4 :
    ((HashAssignmentCompletenessSmall.kit4).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit4).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 5) := by decide

private theorem sorted5 :
    ((HashAssignmentCompletenessSmall.kit5).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit5).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 6) := by decide

private theorem sorted6 :
    ((HashAssignmentCompletenessSmall.kit6).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit6).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 7) := by decide

private theorem sorted7 :
    ((HashAssignmentCompletenessSmall.kit7).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit7).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 8) := by decide

private theorem sorted8 :
    ((HashAssignmentCompletenessSmall.kit8).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit8).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 9) := by decide

private theorem sorted9 :
    ((HashAssignmentCompletenessSmall.kit9).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit9).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 10) := by decide

private theorem sorted10 :
    ((HashAssignmentCompletenessSmall.kit10).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit10).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 11) := by decide

private theorem sorted11 :
    ((HashAssignmentCompletenessSmall.kit11).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit11).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 12) := by decide

private theorem sorted12 :
    ((HashAssignmentCompletenessSmall.kit12).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit12).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 13) := by decide

private theorem sorted13 :
    ((HashAssignmentCompletenessSmall.kit13).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit13).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 14) := by decide

private theorem sorted14 :
    ((HashAssignmentCompletenessSmall.kit14).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit14).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 15) := by decide

private theorem sorted15 :
    ((HashAssignmentCompletenessSmall.kit15).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit15).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 16) := by decide

private theorem sorted16 :
    ((HashAssignmentCompletenessSmall.kit16).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit16).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 17) := by decide

private theorem sorted17 :
    ((HashAssignmentCompletenessSmall.kit17).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit17).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 18) := by decide

private theorem sorted18 :
    ((HashAssignmentCompletenessSmall.kit18).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit18).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 19) := by decide

private theorem sorted19 :
    ((HashAssignmentCompletenessSmall.kit19).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit19).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 20) := by decide

private theorem sorted20 :
    ((HashAssignmentCompletenessSmall.kit20).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit20).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 21) := by decide

private theorem sorted21 :
    ((HashAssignmentCompletenessSmall.kit21).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit21).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 22) := by decide

private theorem sorted22 :
    ((HashAssignmentCompletenessSmall.kit22).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit22).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 23) := by decide

private theorem sorted23 :
    ((HashAssignmentCompletenessSmall.kit23).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit23).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 24) := by decide

private theorem sorted24 :
    ((HashAssignmentCompletenessSmall.kit24).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit24).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 25) := by decide

private theorem sorted25 :
    ((HashAssignmentCompletenessSmall.kit25).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit25).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 26) := by decide

private theorem sorted26 :
    ((HashAssignmentCompletenessSmall.kit26).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit26).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 27) := by decide

private theorem sorted27 :
    ((HashAssignmentCompletenessSmall.kit27).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit27).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 28) := by decide

private theorem sorted28 :
    ((HashAssignmentCompletenessSmall.kit28).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit28).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 29) := by decide

private theorem sorted29 :
    ((HashAssignmentCompletenessSmall.kit29).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit29).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 30) := by decide

private theorem sorted30 :
    ((HashAssignmentCompletenessSmall.kit30).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit30).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 31) := by decide

private theorem sorted31 :
    ((HashAssignmentCompletenessSmall.kit31).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit31).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 32) := by decide

private theorem sorted32 :
    ((HashAssignmentCompletenessSmall.kit32).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit32).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 33) := by decide

private theorem sorted33 :
    ((HashAssignmentCompletenessSmall.kit33).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit33).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 34) := by decide

private theorem sorted34 :
    ((HashAssignmentCompletenessSmall.kit34).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit34).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 35) := by decide

private theorem sorted35 :
    ((HashAssignmentCompletenessSmall.kit35).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit35).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 36) := by decide

private theorem sorted36 :
    ((HashAssignmentCompletenessSmall.kit36).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit36).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 37) := by decide

private theorem sorted37 :
    ((HashAssignmentCompletenessSmall.kit37).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit37).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 38) := by decide

private theorem sorted38 :
    ((HashAssignmentCompletenessSmall.kit38).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit38).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 39) := by decide

private theorem sorted39 :
    ((HashAssignmentCompletenessSmall.kit39).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit39).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 40) := by decide

private theorem sorted40 :
    ((HashAssignmentCompletenessSmall.kit40).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit40).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 41) := by decide

private theorem sorted41 :
    ((HashAssignmentCompletenessSmall.kit41).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit41).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 42) := by decide

private theorem sorted42 :
    ((HashAssignmentCompletenessSmall.kit42).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit42).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 43) := by decide

private theorem sorted43 :
    ((HashAssignmentCompletenessSmall.kit43).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit43).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 44) := by decide

private theorem sorted44 :
    ((HashAssignmentCompletenessSmall.kit44).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit44).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 45) := by decide

private theorem sorted45 :
    ((HashAssignmentCompletenessSmall.kit45).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit45).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 46) := by decide

private theorem sorted46 :
    ((HashAssignmentCompletenessSmall.kit46).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit46).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 47) := by decide

private theorem sorted47 :
    ((HashAssignmentCompletenessSmall.kit47).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit47).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 48) := by decide

private theorem sorted48 :
    ((HashAssignmentCompletenessSmall.kit48).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit48).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 49) := by decide

private theorem sorted49 :
    ((HashAssignmentCompletenessSmall.kit49).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit49).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 50) := by decide

private theorem sorted50 :
    ((HashAssignmentCompletenessSmall.kit50).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit50).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 51) := by decide

private theorem sorted51 :
    ((HashAssignmentCompletenessSmall.kit51).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit51).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 52) := by decide

private theorem sorted52 :
    ((HashAssignmentCompletenessSmall.kit52).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit52).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 53) := by decide

private theorem sorted53 :
    ((HashAssignmentCompletenessSmall.kit53).plan.written ++
      powerWires (HashAssignmentCompletenessSmall.kit53).powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 54) := by decide

/-- Both directions bind the write set to all actual affine and power writes. -/
theorem small_writes (i : Fin 54) (wire : ℕ) :
    writes (smallPart i) wire ↔
      wire ∈ (HashAssignmentCompletenessSmall.kit i).plan.written ∨
      ∃ k, (HashAssignmentCompletenessSmall.kit i).powers.wire k = wire := by
  fin_cases i
  · change writes 1 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit0.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit0.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 1 sorted0 wire
  · change writes 2 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit1.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit1.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 2 sorted1 wire
  · change writes 3 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit2.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit2.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 3 sorted2 wire
  · change writes 4 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit3.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit3.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 4 sorted3 wire
  · change writes 5 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit4.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit4.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 5 sorted4 wire
  · change writes 6 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit5.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit5.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 6 sorted5 wire
  · change writes 7 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit6.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit6.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 7 sorted6 wire
  · change writes 8 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit7.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit7.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 8 sorted7 wire
  · change writes 9 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit8.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit8.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 9 sorted8 wire
  · change writes 10 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit9.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit9.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 10 sorted9 wire
  · change writes 11 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit10.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit10.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 11 sorted10 wire
  · change writes 12 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit11.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit11.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 12 sorted11 wire
  · change writes 13 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit12.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit12.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 13 sorted12 wire
  · change writes 14 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit13.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit13.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 14 sorted13 wire
  · change writes 15 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit14.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit14.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 15 sorted14 wire
  · change writes 16 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit15.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit15.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 16 sorted15 wire
  · change writes 17 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit16.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit16.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 17 sorted16 wire
  · change writes 18 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit17.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit17.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 18 sorted17 wire
  · change writes 19 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit18.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit18.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 19 sorted18 wire
  · change writes 20 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit19.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit19.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 20 sorted19 wire
  · change writes 21 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit20.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit20.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 21 sorted20 wire
  · change writes 22 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit21.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit21.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 22 sorted21 wire
  · change writes 23 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit22.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit22.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 23 sorted22 wire
  · change writes 24 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit23.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit23.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 24 sorted23 wire
  · change writes 25 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit24.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit24.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 25 sorted24 wire
  · change writes 26 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit25.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit25.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 26 sorted25 wire
  · change writes 27 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit26.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit26.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 27 sorted26 wire
  · change writes 28 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit27.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit27.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 28 sorted27 wire
  · change writes 29 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit28.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit28.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 29 sorted28 wire
  · change writes 30 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit29.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit29.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 30 sorted29 wire
  · change writes 31 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit30.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit30.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 31 sorted30 wire
  · change writes 32 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit31.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit31.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 32 sorted31 wire
  · change writes 33 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit32.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit32.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 33 sorted32 wire
  · change writes 34 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit33.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit33.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 34 sorted33 wire
  · change writes 35 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit34.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit34.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 35 sorted34 wire
  · change writes 36 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit35.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit35.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 36 sorted35 wire
  · change writes 37 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit36.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit36.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 37 sorted36 wire
  · change writes 38 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit37.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit37.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 38 sorted37 wire
  · change writes 39 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit38.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit38.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 39 sorted38 wire
  · change writes 40 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit39.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit39.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 40 sorted39 wire
  · change writes 41 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit40.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit40.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 41 sorted40 wire
  · change writes 42 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit41.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit41.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 42 sorted41 wire
  · change writes 43 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit42.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit42.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 43 sorted42 wire
  · change writes 44 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit43.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit43.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 44 sorted43 wire
  · change writes 45 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit44.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit44.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 45 sorted44 wire
  · change writes 46 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit45.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit45.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 46 sorted45 wire
  · change writes 47 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit46.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit46.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 47 sorted46 wire
  · change writes 48 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit47.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit47.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 48 sorted47 wire
  · change writes 49 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit48.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit48.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 49 sorted48 wire
  · change writes 50 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit49.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit49.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 50 sorted49 wire
  · change writes 51 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit50.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit50.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 51 sorted50 wire
  · change writes 52 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit51.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit51.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 52 sorted51 wire
  · change writes 53 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit52.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit52.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 53 sorted52 wire
  · change writes 54 wire ↔ wire ∈ HashAssignmentCompletenessSmall.kit53.plan.written ∨
      ∃ k, HashAssignmentCompletenessSmall.kit53.powers.wire k = wire
    simpa only [List.mem_append, mem_powerWires] using
      sorted_membership _ 54 sorted53 wire

theorem small_preserves (i : Fin 54) (seed : Assignment) (wire : ℕ)
    (h : ¬ writes (smallPart i) wire) :
    HashAssignmentCompletenessSmall.assignment i seed wire = seed wire := by
  rw [small_writes] at h
  exact HashAssignmentCompletenessSmall.preserves i seed wire
    (fun hw => h (Or.inl hw)) (fun k hk => h (Or.inr ⟨k, hk⟩))

theorem small_output_form (i : Fin 54) :
    (SmallHashGatesData.gate i).outputForm =
      [(outputWire ⟨i.val + 1, by omega⟩, 1)] := by
  fin_cases i <;> rfl

private theorem beta_sorted :
    (AssignmentRecoveryBetaData.plan.written ++
      powerWires HashAssignmentCompletenessBetaData.powers).insertionSort
        (fun x y => x ≤ y) = spanWires (spans 0) := by decide

theorem beta_writes (wire : ℕ) :
    writes 0 wire ↔ wire ∈ AssignmentRecoveryBetaData.plan.written ∨
      ∃ k, HashAssignmentCompletenessBetaData.powers.wire k = wire := by
  simpa only [List.mem_append, mem_powerWires] using sorted_membership _ 0 beta_sorted wire

theorem range_writes (wire : ℕ) : writes 55 wire ↔ RangeAssignmentCompleteness.written wire := by
  unfold writes
  rw [show spans 55 = [(569, 728), (13918, 14839)] from rfl]
  simp [RangeAssignmentCompleteness.written]

theorem control_writes (wire : ℕ) : writes 56 wire ↔ wire ∈ ControlCompleteness.writeSet := by
  unfold writes
  rw [show spans 56 = [(728, 730), (13904, 13918), (14839, 14842)] from rfl]
  simp [ControlCompleteness.writeSet]
  omega

theorem gamma_writes (wire : ℕ) : writes 57 wire ↔ wire ∈ GammaCompleteness.writeSet := by
  unfold writes
  rw [show spans 57 = [(103, 111)] from rfl]
  simp [GammaCompleteness.writeSet]

theorem path_writes (wire : ℕ) : ¬ writes 58 wire := by
  unfold writes
  rw [show spans 58 = [] from rfl]
  simp

/-- Existing exact fragment coverage transfers to these fixed part indices. -/
theorem coverage {c : Constraint} (hc : c ∈ Spend.system.constraints) :
    ∃ i : Fin 59, c ∈ constraints i := by
  obtain ⟨family, hf⟩ := ConstraintCoverage.covers hc
  cases family with
  | gamma => exact ⟨57, hf⟩
  | beta => exact ⟨0, hf⟩
  | small i => exact ⟨smallPart i, by rw [constraints_small]; exact hf⟩
  | ranges => exact ⟨55, hf⟩
  | controls => exact ⟨56, hf⟩
  | paths => exact ⟨58, hf⟩

#print axioms small_writes
#print axioms small_preserves
#print axioms small_output_form
#print axioms beta_writes
#print axioms coverage

end MSP.Artifacts.CircuitAssemblyLayout
