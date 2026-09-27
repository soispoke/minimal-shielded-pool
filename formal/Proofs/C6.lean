import Proofs.PoseidonConstants
import Sanity.C6Proof

namespace MSP

attribute [local irreducible] Poseidon.hash2

private theorem h2_eq_hash2 (a b : F) : H2 a b = Poseidon.hash2 a b := by
  delta H2
  exact Eq.refl (Poseidon.hash2 a b)

/-- The specification's zero hashes use the concrete reference permutation. -/
theorem z_eq_zeroHash (l : ℕ) : Z l = Poseidon.zeroHash l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change H2 (Z l) (Z l) = Poseidon.hash2 (Poseidon.zeroHash l) (Poseidon.zeroHash l)
    exact (congrArg₂ H2 ih ih).trans (h2_eq_hash2 _ _)

theorem zero_constants (l : ℕ) (hl : l < DEPTH) : zeroConst l = Z l := by
  rw [z_eq_zeroHash]
  exact poseidon_zero_constants_lt l hl

/-- C6 for the specified incremental-tree algorithm and concrete Poseidon.
The bytecode refinement to this algorithm is a separate chain obligation. -/
theorem c6 : C6 := by
  refine ⟨zero_constants, ?_, C6_third zero_constants⟩
  rw [EMPTY_ROOT, z_eq_zeroHash]
  exact poseidon_empty_root.symm

#print axioms c6

end MSP
