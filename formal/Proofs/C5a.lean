import Sanity.Mono

/-! C5a from C1: every leaf opens to a positive value below `2 ^ 128` and is no
sink, or the run has a bad event. -/

namespace MSP
noncomputable section
open Classical

def GoodPair (c : F) (v : ℕ) : Prop :=
  0 < v ∧ v < 2 ^ 128 ∧ c ≠ SINK 0 ∧ c ≠ SINK 1 ∧ ∃ inr, c = cm inr (v : F)

def Inv (s : PoolState) : Prop := ∀ e, List.Forall₂ GoodPair (s.leaves e) (s.vals e)

theorem forall₂_new (new : List (F × ℕ)) (h : ∀ x ∈ new, GoodPair x.1 x.2) :
    List.Forall₂ GoodPair (new.map Prod.fst) (new.map Prod.snd) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  exact h

theorem inv_append (s : PoolState) (new : List (F × ℕ)) (hs : Inv s)
    (h : ∀ x ∈ new, GoodPair x.1 x.2) : Inv (s.append new) := by
  intro e
  unfold PoolState.append
  split_ifs <;>
  · simp only [Function.update_apply]
    split_ifs
    · exact List.rel_append (hs _) (forall₂_new new h)
    · exact hs e

theorem natCast_val_eq {n : ℕ} (hn : n < p) {c : F} (h : (n : F) = c) : n = c.val := by
  rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hn]

theorem newLeaves_good (sd : SettleData) (w : Witness) (hR : R sd.stmt w)
    (ho1 : sd.o1 < p) (ho2 : sd.o2 < p) (hs1 : sd.o1 ≠ (SINK 1).val) (hs0 : sd.o2 ≠ (SINK 0).val) :
    ∀ x ∈ newLeaves sd w, GoodPair x.1 x.2 := by
  obtain ⟨-, -, -, -, hco1, hco2, hrange, -, -, hR7, -⟩ := hR
  simp only [SettleData.stmt] at hco1 hco2
  intro x hx
  unfold newLeaves at hx
  have hov0 : (w.ov 0).val < 2 ^ 128 := hrange _ (by simp)
  have hov1 : (w.ov 1).val < 2 ^ 128 := hrange _ (by simp)
  split_ifs at hx with h0 h1 h1
  · simp at hx
  · simp at hx; subst hx
    refine ⟨?_, hov1, ?_, ?_, w.oi 1, by simpa using hco2⟩
    · by_contra hz
      have hz' : w.ov 1 = 0 := by
        rw [Nat.pos_iff_ne_zero, not_not] at hz; exact (ZMod.val_eq_zero _).mp hz
      have := (hR7 1).1 hz'
      apply h1; apply natCast_val_eq ho2
      rw [hco2, this, hz']; rfl
    · intro h; exact hs0 (natCast_val_eq ho2 h)
    · intro h; exact h1 (natCast_val_eq ho2 h)
  · simp at hx; subst hx
    refine ⟨?_, hov0, ?_, ?_, w.oi 0, by simpa using hco1⟩
    · by_contra hz
      have hz' : w.ov 0 = 0 := by
        rw [Nat.pos_iff_ne_zero, not_not] at hz; exact (ZMod.val_eq_zero _).mp hz
      have := (hR7 0).1 hz'
      apply h0; apply natCast_val_eq ho1
      rw [hco1, this, hz']; rfl
    · intro h; exact h0 (natCast_val_eq ho1 h)
    · intro h; exact hs1 (natCast_val_eq ho1 h)
  · simp at hx
    rcases hx with rfl | rfl
    · refine ⟨?_, hov0, ?_, ?_, w.oi 0, by simpa using hco1⟩
      · by_contra hz
        have hz' : w.ov 0 = 0 := by
          rw [Nat.pos_iff_ne_zero, not_not] at hz; exact (ZMod.val_eq_zero _).mp hz
        have := (hR7 0).1 hz'
        apply h0; apply natCast_val_eq ho1
        rw [hco1, this, hz']; rfl
      · intro h; exact h0 (natCast_val_eq ho1 h)
      · intro h; exact hs1 (natCast_val_eq ho1 h)
    · refine ⟨?_, hov1, ?_, ?_, w.oi 1, by simpa using hco2⟩
      · by_contra hz
        have hz' : w.ov 1 = 0 := by
          rw [Nat.pos_iff_ne_zero, not_not] at hz; exact (ZMod.val_eq_zero _).mp hz
        have := (hR7 1).1 hz'
        apply h1; apply natCast_val_eq ho2
        rw [hco2, this, hz']; rfl
      · intro h; exact hs0 (natCast_val_eq ho2 h)
      · intro h; exact h1 (natCast_val_eq ho2 h)

theorem c5a_inv (P : Pool) (hC1 : C1) : ∀ evs s, Run P evs s → BadEvent P evs s ∨ Inv s := by
  intro evs s h
  induction h with
  | nil => right; intro e; simp [PoolState.init]
  | @snoc evs s e s' hrun hs ih =>
    rcases ih with hb | hinv
    · left; exact bad_mono P (List.prefix_append _ _) (grows_step P s s' e hs) [] hb
    cases e with
    | shield inr v =>
      obtain ⟨h0, h128, hs0, hs1, -, rfl⟩ := hs
      right
      have := inv_append s [(cm inr v, v)] hinv (by
        intro x hx; simp at hx; subst hx; exact ⟨h0, h128, hs0, hs1, inr, rfl⟩)
      exact this
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact Or.inr hinv
    | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; exact Or.inr hinv
    | claim r0 => obtain ⟨-, -, rfl⟩ := hs; exact Or.inr hinv
    | receive v => subst hs; exact Or.inr hinv
    | tick => subst hs; exact Or.inr hinv
    | spend tx g =>
      by_cases hx : Satisfied (extOf P tx) ∧ publicOf (extOf P tx) = verifiedPublics tx
      swap
      · left; right; right; right; exact ⟨tx, g, by simp, hx⟩
      by_cases hcb : stmtOf (extOf P tx) = (settleData tx).stmt
      swap
      · left; right; right; left; exact ⟨tx, g, by simp, hx.1, hx.2, hcb⟩
      have hR := (hC1 _ hx.1).1
      rw [hcb] at hR
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
      right
      split_ifs with hpre hpub
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ho1, ho2, -, -, -, -, hs1, hs0, -⟩ := hpre
        exact inv_append _ _ hinv (newLeaves_good _ _ hR ho1 ho2 hs1 hs0)
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ho1, ho2, -, -, -, -, hs1, hs0, -⟩ := hpre
        exact inv_append _ _ hinv (newLeaves_good _ _ hR ho1 ho2 hs1 hs0)
      · exact hinv

theorem c5a (P : Pool) (hC1 : C1) : C5a P := by
  intro evs s h
  rcases c5a_inv P hC1 evs s h with hb | hinv
  · exact Or.inl hb
  right
  intro e i hi
  have hf := hinv e
  have hl := hf.length_eq
  rw [List.forall₂_iff_get] at hf
  obtain ⟨-, hg⟩ := hf
  have hi' : i < (s.vals e).length := hl ▸ hi
  have := hg i hi hi'
  simp only [List.get_eq_getElem] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some]
  obtain ⟨a, b, c, d, f⟩ := this
  exact ⟨hl.symm, a, b, c, d, f⟩

end
end MSP
