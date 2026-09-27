import Artifacts.PathBitsData
import Artifacts.RangeGate
import Artifacts.Spend

/-!
# Concrete path indices

The two index projections are the little-endian values of the actual private
path-bit wires. Their bounds follow from forty exact pinned Boolean constraints.
Connecting those indices to the optimized Poseidon/path gadgets is separate.
-/

namespace MSP.Artifacts.PathBits

open RangeGate RangeLemmas

/-- Exact constraint locations in the full pinned system. -/
theorem path0_eq_slice :
    PathBitsData.path0Constraints = (Spend.group2.drop 124).take 20 := rfl

theorem path1_eq_slice :
    PathBitsData.path1Constraints = (Spend.group27.drop 76).take 20 := rfl

private theorem constraints_mem (k : Fin 2) {c : Constraint}
    (hc : c ∈ PathBitsData.constraints k) : c ∈ Spend.system.constraints := by
  fin_cases k
  · change c ∈ PathBitsData.path0Constraints at hc
    rw [path0_eq_slice] at hc
    exact List.mem_flatten.mpr
      ⟨Spend.group2, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩
  · change c ∈ PathBitsData.path1Constraints at hc
    rw [path1_eq_slice] at hc
    exact List.mem_flatten.mpr
      ⟨Spend.group27, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem constraints_eq (k : Fin 2) :
    PathBitsData.constraints k =
      (List.range DEPTH).map (lowConstraint (PathBitsData.bitStart k)) := by
  fin_cases k <;> rfl

private theorem wire_list_eq (k : Fin 2) :
    PathBitsData.bitWires k = (List.range DEPTH).map (fun i => PathBitsData.bitStart k + i) := by
  fin_cases k <;> rfl

/-- Actual private input path bits, in increasing little-endian position. -/
def bits (w : Assignment) (k : Fin 2) : List F := (PathBitsData.bitWires k).map w

/-- Natural index carried by those bits. -/
def index (w : Assignment) (k : Fin 2) : ℕ := bitsValue (bits w k)

theorem bits_eq (w : Assignment) (k : Fin 2) :
    bits w k = (List.range DEPTH).map (fun i => w (PathBitsData.bitStart k + i)) := by
  rw [bits, wire_list_eq, List.map_map]
  rfl

theorem bit_boolean (w : Assignment) (h : Spend.system.Satisfied w)
    (k : Fin 2) (i : ℕ) (hi : i < DEPTH) :
    w (PathBitsData.bitStart k + i) * (w (PathBitsData.bitStart k + i) - 1) = 0 := by
  have hm : lowConstraint (PathBitsData.bitStart k) i ∈ PathBitsData.constraints k := by
    rw [constraints_eq]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hc := h.2 _ (constraints_mem k hm)
  simp only [lowConstraint, Constraint.Holds, LinearCombination.eval, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] at hc
  rw [coefficient_neg_one, h.1] at hc
  linear_combination hc

/-- R1's bound follows from the actual forty Boolean constraints. -/
theorem index_bounded (w : Assignment) (h : Spend.system.Satisfied w) (k : Fin 2) :
    index w k < 2^DEPTH := by
  have hb : ∀ b ∈ bits w k, b * (b - 1) = 0 := by
    intro b hb
    rw [bits_eq] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact bit_boolean w h k i (List.mem_range.mp hi)
  have bound := bitsValue_lt (bits w k) hb
  simpa only [index, bits_eq, List.length_map, List.length_range] using bound

/-- Exact cast from the natural index to the raw weighted field expression.
This equality itself holds for every assignment; Booleanity supplies the bound. -/
theorem index_cast (w : Assignment) (k : Fin 2) :
    (index w k : F) = (weightedWires (PathBitsData.bitStart k) DEPTH).eval w := by
  rw [index, bitsValue_cast, bits_eq, bitsField_range, weightedWires_eval]

end MSP.Artifacts.PathBits
