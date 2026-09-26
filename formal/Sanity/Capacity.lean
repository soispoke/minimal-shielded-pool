import Spec

/-! Every epoch holds at most `CAPACITY` leaves in every model run, so
an occurrence index is below `2 ^ DEPTH` (Spendable's R1 and the tree lemma's
premise). -/

namespace MSP
noncomputable section
open Classical

def CapInv (s : PoolState) : Prop :=
  (∀ e, (s.leaves e).length ≤ CAPACITY) ∧ (∀ e, s.E < e → s.leaves e = [])

theorem capInv_append (s : PoolState) (new : List (F × ℕ)) (hn : new.length ≤ 2) (h : CapInv s) :
    CapInv (s.append new) := by
  obtain ⟨h1, h2⟩ := h
  have hcap : 2 ≤ CAPACITY := by unfold CAPACITY DEPTH; norm_num
  unfold PoolState.append rollsOver
  split_ifs with hr
  · refine ⟨fun e => ?_, fun e he => ?_⟩
    · simp only [Function.update_apply]
      split_ifs with hee
      · subst hee; rw [h2 _ (Nat.lt_succ_self _)]; simp; omega
      · exact h1 e
    · simp only [Function.update_apply] at he ⊢
      rw [if_neg (by omega)]; exact h2 e (by omega)
  · refine ⟨fun e => ?_, fun e he => ?_⟩
    · simp only [Function.update_apply]
      split_ifs with hee
      · subst hee; simp; have := h1 s.E; omega
      · exact h1 e
    · simp only [Function.update_apply] at he ⊢
      rw [if_neg (by omega)]; exact h2 e he

theorem newLeaves_len (sd : SettleData) (w : Witness) : (newLeaves sd w).length ≤ 2 := by
  unfold newLeaves; split_ifs <;> simp

theorem capInv_run (P : Pool) : ∀ evs s, Run P evs s → CapInv s := by
  intro evs s h
  induction h with
  | nil => exact ⟨fun _ => by simp [PoolState.init], fun _ _ => rfl⟩
  | @snoc evs s e s' _ hs ih =>
    cases e with
    | shield inr v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      have := capInv_append s [(cm inr v, v)] (by simp) ih
      exact ⟨this.1, this.2⟩
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact ih
    | rootWrite a salt r => obtain ⟨-, -, rfl⟩ := hs; exact ih
    | claim r => obtain ⟨-, -, rfl⟩ := hs; exact ih
    | receive v => subst hs; exact ih
    | tick => subst hs; exact ih
    | spend tx g =>
      obtain ⟨-, -, -, -, -, -, -, hs'⟩ := hs
      rw [hs']
      have ih1 : CapInv { s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)), balance := s.balance - g } := ⟨ih.1, ih.2⟩
      split_ifs
      · have := capInv_append _ _ (newLeaves_len (settleData tx) (witOf (extOf P tx))) ih1
        exact ⟨this.1, this.2⟩
      · have := capInv_append _ _ (newLeaves_len (settleData tx) (witOf (extOf P tx))) ih1
        exact ⟨this.1, this.2⟩
      · exact ih1

#print axioms capInv_run

end
end MSP
