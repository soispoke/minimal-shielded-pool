import Sanity.Mono

/-! The model's single-spend claim and refinement imply the chain corollary. -/

namespace MSP

noncomputable section

open Classical

private theorem append_spent (s : PoolState) (new : List (F × ℕ)) :
    (s.append new).spent = s.spent := by
  unfold PoolState.append
  split_ifs <;> rfl

private theorem inputs_nodup (sd : SettleData) (w : Witness)
    (hd : w.v 0 ≠ 0 → w.v 1 ≠ 0 → w.idx 0 ≠ w.idx 1) :
    (inputsOf sd w).Nodup := by
  have hr : List.finRange 2 = [0, 1] := by decide
  by_cases h0 : w.v 0 = 0 <;> by_cases h1 : w.v 1 = 0
  · simp [inputsOf, hr, h0, h1]
  · simp [inputsOf, hr, h0, h1]
  · simp [inputsOf, hr, h0, h1]
  · have hi := hd h0 h1
    simp [inputsOf, hr, h0, h1, hi]

/-- C5b excludes a repeated occurrence both within one spend and across spends. -/
theorem spent_nodup_of_c5b (P : Pool) (hC5b : C5b P) :
    ∀ evs s, Run P evs s → BadEvent P evs s ∨ s.spent.Nodup := by
  intro evs s h
  induction h with
  | nil => exact Or.inr (by simp [PoolState.init])
  | @snoc evs s e s' hrun hs ih =>
    rcases ih with hb | hnd
    · exact Or.inl (bad_mono P (List.prefix_append _ _) (grows_step P s s' e hs) [] hb)
    cases e with
    | shield inr v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      exact Or.inr (by simpa only [append_spent] using hnd)
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact Or.inr hnd
    | rootWrite a salt r => obtain ⟨-, -, rfl⟩ := hs; exact Or.inr hnd
    | claim r => obtain ⟨-, -, rfl⟩ := hs; exact Or.inr hnd
    | receive v => subst hs; exact Or.inr hnd
    | tick => subst hs; exact Or.inr hnd
    | spend tx g =>
      rcases hC5b evs s tx g s' hrun hs with hb | ⟨hunspent, hdistinct⟩
      · exact Or.inl hb
      have happ : (s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx))).Nodup := by
        apply List.nodup_append.2
        refine ⟨hnd, inputs_nodup _ _ hdistinct, ?_⟩
        intro o ho o' hin heq
        subst o'
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hin
        have hv : (witOf (extOf P tx)).v k ≠ 0 := by
          simpa only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using hk
        exact (hunspent k hv).2.2.2 ho
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
      right
      split_ifs <;> simpa only [append_spent] using happ

/-- The main theorem supplies the model invariants for every refined chain run. -/
theorem composes : Composes := by
  rintro ⟨hC1, _, hmodel, hchain⟩ d ext hhonest h hrun
  obtain ⟨_, _, _, _, _, _, hrefines⟩ := hchain
  obtain ⟨_, _, _, hC5b, hC5c, _, hC5e, _⟩ := hmodel hC1 (poolOf d ext)
  rcases (hrefines d ext hhonest h hrun).1 with ⟨s, hs, hobs⟩ | hbad
  · right
    refine ⟨s, hs, ?_⟩
    rcases hobs with hb | hobs
    · exact Or.inl hb
    rcases hC5c _ _ hs with hb | hsolvent
    · exact Or.inl hb
    rcases spent_nodup_of_c5b _ hC5b _ _ hs with hb | hnodup
    · exact Or.inl hb
    right
    refine ⟨hobs, hsolvent, hnodup, ?_⟩
    intro r hr e he hsrc
    rcases hC5e _ _ hs r hr e he hsrc with hb | ⟨_, hroot⟩
    · exact Or.inl hb
    · exact Or.inr hroot
  · exact Or.inl hbad

#print axioms spent_nodup_of_c5b
#print axioms composes

end

end MSP
