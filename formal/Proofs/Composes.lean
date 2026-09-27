import Spec
import Sanity.Mono
import Proofs.Effects

/-! `Composes`: the main theorem implies `ChainCorollary`. -/

namespace MSP
noncomputable section
open Classical

theorem append_spent (s : PoolState) (new : List (F × ℕ)) : (s.append new).spent = s.spent := by
  unfold PoolState.append; split_ifs <;> rfl

theorem inputs_nodup (sd : SettleData) (w : Witness)
    (hd : w.v 0 ≠ 0 → w.v 1 ≠ 0 → w.idx 0 ≠ w.idx 1) : (inputsOf sd w).Nodup := by
  unfold inputsOf
  by_cases h0 : w.v 0 = 0 <;> by_cases h1 : w.v 1 = 0 <;>
    simp [List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, h0, h1, List.filter]
  intro h; exact hd h0 h1 (by simpa using h)

theorem run_nodup (P : Pool) (h5b : C5b P) :
    ∀ evs s, Run P evs s → BadEvent P evs s ∨ s.spent.Nodup := by
  intro evs s hr
  induction hr with
  | nil => right; simp [PoolState.init]
  | @snoc evs s e s' hr hs ih =>
    have hg := grows_step P s s' e hs
    have hpre : evs <+: evs ++ [e] := List.prefix_append _ _
    rcases ih with hb | hn
    · exact Or.inl (bad_mono P hpre hg [] hb)
    cases e with
    | spend tx g =>
      rcases h5b evs s tx g s' hr hs with hb | ⟨hk, hd⟩
      · exact Or.inl hb
      right
      have hsp : s'.spent = s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)) := by
        obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
        split_ifs <;> simp [append_spent]
      rw [hsp, List.nodup_append]
      refine ⟨hn, inputs_nodup _ _ hd, ?_⟩
      intro a ha b hb hab
      subst hab
      unfold inputsOf at hb
      simp only [List.mem_map, List.mem_filter] at hb
      obtain ⟨k, ⟨-, hk0⟩, rfl⟩ := hb
      exact (hk k (by simpa using hk0)).2.2.2 ha
    | shield inr v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      right; simpa [append_spent] using hn
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact Or.inr hn
    | rootWrite a salt r => obtain ⟨-, -, rfl⟩ := hs; exact Or.inr hn
    | claim r => obtain ⟨-, -, rfl⟩ := hs; exact Or.inr hn
    | receive v => subst hs; exact Or.inr hn
    | tick => subst hs; exact Or.inr hn

theorem composes : Composes := by
  rintro ⟨hC1, -, hMT, -, -, -, -, -, -, hRef⟩
  intro d ext hd h hrun
  obtain ⟨hr1, -⟩ := hRef d ext hd h hrun
  obtain ⟨-, -, -, h5b, h5c, -, h5e, -⟩ := hMT hC1 (poolOf d ext)
  rcases hr1 with ⟨s, hs, hb | hobs⟩ | hpre
  · exact Or.inr ⟨s, hs, Or.inl hb⟩
  · rcases h5c _ _ hs with hb | hsol
    · exact Or.inr ⟨s, hs, Or.inl hb⟩
    rcases run_nodup _ h5b _ _ hs with hb | hnd
    · exact Or.inr ⟨s, hs, Or.inl hb⟩
    refine Or.inr ⟨s, hs, Or.inr ⟨hobs, hsol, hnd, ?_⟩⟩
    intro r hr e he hre
    rcases h5e _ _ hs r hr e he hre with hb | ⟨-, n, hn, heq⟩
    · exact Or.inl hb
    · exact Or.inr ⟨n, hn, heq⟩
  · exact Or.inl hpre

#print axioms run_nodup
#print axioms composes

end
end MSP
