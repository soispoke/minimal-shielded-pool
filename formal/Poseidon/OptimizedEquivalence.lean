import Poseidon.OptimizedReference

/-! The sparse optimized width-11 schedule is related to the ordinary reference
by explicit changes of basis and relocation of round constants. -/

namespace MSP.Poseidon.Optimized

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem mix_add (m : Matrix11) (s t : State) :
    mix m (s + t) = mix m s + mix m t := Matrix.add_vecMul _ _ _

private theorem mix_mix (a b : Matrix11) (s : State) :
    mix b (mix a s) = mix (a * b) s := Matrix.vecMul_vecMul _ _ _

private theorem mix_basis_zero (r : Fin 67) (s : State) : mix (basis r) s 0 = s 0 := by
  simp [mix, Matrix.vecMul, dotProduct, basis_first_column]

private theorem mix_basis_single (r : Fin 67) (d : F) :
    mix (basis r) (single0 d) = single0 d := by
  funext i
  simp [mix, Matrix.vecMul, dotProduct, single0, basis_first_row]

private theorem partialSbox_eq (s : State) :
    partialSbox s = s + single0 (s 0 ^ 5 - s 0) := by
  funext i
  by_cases h : i = 0 <;> simp [partialSbox, single0, h]

private theorem partialSbox_basis (r : Fin 67) (s : State) :
    partialSbox (mix (basis r) s) = mix (basis r) (partialSbox s) := by
  rw [partialSbox_eq, partialSbox_eq, mix_add, mix_basis_zero, mix_basis_single]

private theorem partialSbox_translation (r : Fin 67) (s : State) :
    partialSbox (s + translation r) = partialSbox s + translation r := by
  funext i
  by_cases h : i = 0 <;> simp [partialSbox, h, translation_zero]

private theorem partial_step_bridge (r : Fin 66) (s : State) :
    partialStep r (mix (basis ⟨r.val, by omega⟩) (s + translation ⟨r.val, by omega⟩)) =
      mix (basis ⟨r.val + 1, by omega⟩)
        (mix M (partialSbox s) + referenceConstant ⟨r.val + 5, by omega⟩ +
          translation ⟨r.val + 1, by omega⟩) := by
  unfold partialStep
  rw [partialSbox_basis, ← mix_basis_single ⟨r.val, by omega⟩ (partialConstant r),
    ← mix_add, mix_mix]
  rw [show basis ⟨r.val, by omega⟩ * sparseMatrix r = M * basis ⟨r.val + 1, by omega⟩
    from funext fun i => funext fun j => partial_factors r i j]
  rw [← mix_mix, partialSbox_translation, add_assoc, mix_add]
  rw [show mix M (translation ⟨r.val, by omega⟩ + single0 (partialConstant r)) =
      referenceConstant ⟨r.val + 5, by omega⟩ + translation ⟨r.val + 1, by omega⟩
    from funext fun i => partial_constants r i]
  rw [add_assoc]

private theorem prefix_first_three (inputs : Fin 10 → F) (k : ℕ) (hk : k ≤ 3) :
    run prefixStep (initialState inputs) k = referencePre inputs ⟨k, by omega⟩ := by
  induction k with
  | zero => exact reference_initial inputs
  | succ k ih =>
    rw [run_succ _ _ (by omega), ih (by omega)]
    unfold prefixStep
    rw [ite_eq_right (by change k ≠ 3; omega), mix_add]
    rw [show mix M (prefixConstant ⟨k, by omega⟩) = referenceConstant ⟨k + 1, by omega⟩
      from funext fun i => prefix_constants ⟨k, by omega⟩ i]
    exact (reference_full_next inputs ⟨k, by omega⟩ (Or.inl (by change k < 4; omega))).symm

private theorem prefix_bridge (inputs : Fin 10 → F) :
    prefixState inputs = mix (basis 0) (referencePre inputs 4 + translation 0) := by
  change run prefixStep (initialState inputs) 4 = _
  rw [run_succ _ _ (show 3 < 4 by omega), prefix_first_three inputs 3 (by omega)]
  change mix P (sbox (referencePre inputs 3) + prefixConstant 3) = _
  rw [show P = M * basis 0 from (funext fun i => funext fun j => boundary_basis i j).symm,
    ← mix_mix, mix_add]
  rw [show mix M (prefixConstant 3) = referenceConstant 4 + translation 0
    from funext fun i => boundary_constant i]
  have hn := reference_full_next inputs 3 (Or.inl (by decide))
  norm_num at hn
  rw [← add_assoc, ← hn]

private theorem partial_invariant (inputs : Fin 10 → F) (k : ℕ) (hk : k ≤ 66) :
    run partialStep (prefixState inputs) k =
      mix (basis ⟨k, by omega⟩)
        (referencePre inputs ⟨k + 4, by omega⟩ + translation ⟨k, by omega⟩) := by
  induction k with
  | zero =>
    rw [run_zero]
    rw [show (⟨0, by omega⟩ : Fin 67) = 0 from rfl,
      show (⟨0 + 4, by omega⟩ : Fin 74) = 4 from rfl]
    exact prefix_bridge inputs
  | succ k ih =>
    rw [run_succ _ _ (by omega), ih (by omega), partial_step_bridge]
    have hn := reference_partial_next inputs ⟨k + 4, by omega⟩
      (by constructor <;> simp only [Fin.val_mk] <;> omega)
    simpa only using congrArg
      (fun t => mix (basis ⟨k + 1, by omega⟩) (t + translation ⟨k + 1, by omega⟩)) hn.symm

private theorem partial_bridge (inputs : Fin 10 → F) :
    partialState inputs = referencePre inputs 70 := by
  change run partialStep (prefixState inputs) 66 = _
  rw [partial_invariant inputs 66 (by omega)]
  rw [show (⟨66, by omega⟩ : Fin 67) = 66 from rfl,
    show (⟨66 + 4, by omega⟩ : Fin 74) = 70 from rfl]
  rw [show basis 66 = (1 : Matrix11) from funext fun i => funext fun j => basis_final i j]
  rw [show translation 66 = (0 : State) from funext fun i => translation_final i]
  simp [mix]

private theorem suffix_invariant (inputs : Fin 10 → F) (k : ℕ) (hk : k ≤ 3) :
    run suffixStep (partialState inputs) k = referencePre inputs ⟨70 + k, by omega⟩ := by
  induction k with
  | zero =>
    rw [run_zero, show (⟨70 + 0, by omega⟩ : Fin 74) = 70 from rfl]
    exact partial_bridge inputs
  | succ k ih =>
    rw [run_succ _ _ (by omega), ih (by omega)]
    unfold suffixStep
    rw [mix_add]
    rw [show mix M (suffixConstant ⟨k, by omega⟩) = referenceConstant ⟨71 + k, by omega⟩
      from funext fun i => suffix_constants ⟨k, by omega⟩ i]
    have hn := reference_full_next inputs ⟨70 + k, by omega⟩ (Or.inr (by change 70 ≤ 70 + k; omega))
    simpa only [Fin.val_mk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn.symm

/-- The optimized width-11 function equals the ordinary D2 reference for every
field-valued input. The proof uses exact finite coefficient certificates and
symbolic state invariants, with no assumption about the input. -/
theorem hash10_eq_reference (inputs : Fin 10 → F) :
    hash10 inputs = MSP.Poseidon.hash10 inputs := by
  rw [reference_hash]
  unfold hash10
  have hs : suffixState inputs = referencePre inputs 73 := suffix_invariant inputs 3 (by omega)
  rw [hs]

end MSP.Poseidon.Optimized
