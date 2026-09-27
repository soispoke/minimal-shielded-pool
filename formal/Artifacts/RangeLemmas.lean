import Artifacts.R1CS
import Proofs.CircuitGadgets

/-! Algebraic bridges for Num2Bits gadgets whose highest bit was eliminated by
the optimizer. Actual constraint coefficients and membership in the pinned
system are separate obligations. -/

namespace MSP.Artifacts.RangeLemmas

theorem bitsField_append (bs cs : List F) :
    bitsField (bs ++ cs) = bitsField bs + (2 : F) ^ bs.length * bitsField cs := by
  induction bs with
  | nil => simp [bitsField]
  | cons b bs ih =>
    simp only [List.cons_append, bitsField, List.length_cons, pow_succ, ih]
    ring

theorem bitsField_range (n : ℕ) (f : ℕ → F) :
    bitsField ((List.range n).map f) = ∑ i ∈ Finset.range n, (2 : F) ^ i * f i := by
  induction n with
  | zero => simp [bitsField]
  | succ n ih =>
    rw [List.range_succ, List.map_append, bitsField_append, ih, Finset.sum_range_succ]
    simp [bitsField]

/-- Little-endian coefficients for the consecutive wires holding the low bits. -/
def weightedWires (start n : ℕ) : LinearCombination :=
  (List.range n).map fun i => (start + i, 2 ^ i)

theorem weightedWires_eval (w : Assignment) (start n : ℕ) :
    (weightedWires start n).eval w =
      ∑ i ∈ Finset.range n, (2 : F) ^ i * w (start + i) := by
  induction n with
  | zero => simp [weightedWires, LinearCombination.eval]
  | succ n ih =>
    simp only [weightedWires, List.range_succ, List.map_append, LinearCombination.eval,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Finset.sum_range_succ, Nat.cast_pow, Nat.cast_ofNat] at ih ⊢
    exact congrArg (fun x => x + (2 : F) ^ n * w (start + n)) ih

theorem bitsField_wires_append (w : Assignment) (start n : ℕ) (hi : F) :
    bitsField (((List.range n).map fun i => w (start + i)) ++ [hi]) =
      (weightedWires start n).eval w + (2 : F) ^ n * hi := by
  rw [bitsField_append, bitsField_range, weightedWires_eval]
  simp [bitsField]

/-- Boolean low wires and a Boolean reconstructed high bit bound the input's
integer value once their weighted reconstruction equals that input. -/
theorem num2Bits_wires_range (w : Assignment) (start n : ℕ) (hi x : F)
    (hbits : ∀ i < n, w (start + i) * (w (start + i) - 1) = 0)
    (hhi : hi * (hi - 1) = 0) (hsize : 2 ^ (n + 1) ≤ p)
    (hreconstruct : (weightedWires start n).eval w + (2 : F) ^ n * hi = x) :
    x.val < 2 ^ (n + 1) := by
  have h := num2Bits_range x (((List.range n).map fun i => w (start + i)) ++ [hi])
    (by
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        exact hbits i (List.mem_range.1 hi)
      · have heq := List.mem_singleton.1 hb
        simpa only [heq] using hhi)
    (by simpa using hsize)
    ((bitsField_wires_append w start n hi).trans hreconstruct)
  simpa using h

#print axioms bitsField_append
#print axioms bitsField_range
#print axioms weightedWires_eval
#print axioms bitsField_wires_append
#print axioms num2Bits_wires_range

end MSP.Artifacts.RangeLemmas
