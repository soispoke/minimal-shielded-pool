import Spec

/-! C5d: each credit is what was credited minus what was paid, by construction. -/

namespace MSP
noncomputable section
open Classical

theorem append_credit (s : PoolState) (new : List (F × ℕ)) :
    (s.append new).credit = s.credit ∧ (s.append new).paid = s.paid ∧ (s.append new).credited = s.credited := by
  unfold PoolState.append; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem c5d (P : Pool) : C5d P := by
  intro evs s h
  induction h with
  | nil => intro r; simp [PoolState.init]
  | @snoc evs s e s' _ hs ih =>
    intro r
    cases e with
    | shield inr v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      obtain ⟨h1, h2, h3⟩ := append_credit s [(cm inr v, v)]
      simpa [h1, h2, h3] using ih r
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact ih r
    | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; exact ih r
    | claim r0 =>
      obtain ⟨-, -, rfl⟩ := hs
      by_cases hr : r = r0
      · subst hr; simp; have := ih r; omega
      · simp [Finsupp.erase_ne hr, Finsupp.single_apply, Ne.symm hr]; exact ih r
    | receive v => subst hs; exact ih r
    | tick => subst hs; exact ih r
    | spend tx g =>
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
      split_ifs with h1 h2
      · obtain ⟨a1, a2, a3⟩ := append_credit
          { s with keys := s.keys ++ tx.nonceKeys,
                   spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
                   balance := s.balance - g } (newLeaves (settleData tx) (witOf (extOf P tx)))
        simp only [a1, a2, a3]; exact ih r
      · obtain ⟨a1, a2, a3⟩ := append_credit
          { s with keys := s.keys ++ tx.nonceKeys,
                   spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
                   balance := s.balance - g } (newLeaves (settleData tx) (witOf (extOf P tx)))
        simp only [Finsupp.add_apply, a1, a2, a3]; have := ih r; omega
      · exact ih r

#print axioms c5d
end
end MSP
