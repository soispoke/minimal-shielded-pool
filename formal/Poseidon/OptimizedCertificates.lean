import Poseidon.Optimized

/-! Finite algebra certificates connecting the pinned optimized constants to
the ordinary reference. Every certificate is checked by the Lean kernel. -/

namespace MSP.Poseidon.Optimized

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def referenceConstant (r : Fin 74) : State := fun i => (params11.constants.get r).get i

theorem matrix_reference : ∀ i j : Fin 11, M i j = (params11.matrix.get j).get i := by
  unfold M
  decide

theorem initial_constant : ∀ i : Fin 11, C ⟨i.val, by omega⟩ = referenceConstant 0 i := by
  decide

theorem prefix_constants : ∀ r : Fin 3, ∀ i : Fin 11,
    mix M (prefixConstant ⟨r.val, by omega⟩) i = referenceConstant ⟨r.val + 1, by omega⟩ i := by
  decide

theorem boundary_constant : ∀ i : Fin 11,
    mix M (prefixConstant 3) i = (referenceConstant 4 + translation 0) i := by
  decide

theorem suffix_constants : ∀ r : Fin 3, ∀ i : Fin 11,
    mix M (suffixConstant r) i = referenceConstant ⟨71 + r.val, by omega⟩ i := by
  decide

theorem basis_first_row : ∀ r : Fin 67, ∀ i : Fin 11,
    basis r 0 i = if i = 0 then 1 else 0 := by
  decide

theorem basis_first_column : ∀ r : Fin 67, ∀ i : Fin 11,
    basis r i 0 = if i = 0 then 1 else 0 := by
  decide

theorem basis_final : ∀ i j : Fin 11, basis 66 i j = (1 : Matrix11) i j := by
  simp only [Matrix.one_apply]
  unfold basis
  decide

theorem translation_zero : ∀ r : Fin 67, translation r 0 = 0 := by
  decide

theorem translation_final : ∀ i : Fin 11, translation 66 i = 0 := by
  decide

theorem boundary_basis : ∀ i j : Fin 11, (M * basis 0) i j = P i j := by
  unfold P
  decide

theorem partial_factors : ∀ r : Fin 66, ∀ i j : Fin 11,
    (basis ⟨r.val, by omega⟩ * sparseMatrix r) i j =
      (M * basis ⟨r.val + 1, by omega⟩) i j := by
  decide

theorem partial_constants : ∀ r : Fin 66, ∀ i : Fin 11,
    mix M (translation ⟨r.val, by omega⟩ + single0 (partialConstant r)) i =
      (referenceConstant ⟨r.val + 5, by omega⟩ + translation ⟨r.val + 1, by omega⟩) i := by
  decide

end MSP.Poseidon.Optimized
