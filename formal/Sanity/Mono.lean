import Spec

/-! Every model-claim proof (C4, C5a to C5c, Composes) must
push a bad event found at one step to a later prefix of the run. That needs
`traceQueries` to be monotone along `Step`, which this file proves. The trace reads `s.roots`, `s.E`
and every prefix of every epoch's leaves, so it suffices that no step shrinks
the roots, the epoch or any epoch's leaves. -/

namespace MSP
noncomputable section
open Classical

structure Grows (s s' : PoolState) : Prop where
  roots : s.roots <+: s'.roots
  E : s.E ≤ s'.E
  leaves : ∀ e, s.leaves e <+: s'.leaves e

theorem Grows.refl (s : PoolState) : Grows s s := ⟨List.prefix_refl _, le_rfl, fun _ => List.prefix_refl _⟩

theorem Grows.same {s s' : PoolState} (h1 : s'.roots = s.roots) (h2 : s'.E = s.E) (h3 : s'.leaves = s.leaves) : Grows s s' :=
  ⟨by rw [h1], by rw [h2], fun e => by rw [h3]⟩

theorem Grows.trans {a b c : PoolState} (h1 : Grows a b) (h2 : Grows b c) : Grows a c :=
  ⟨h1.roots.trans h2.roots, h1.E.trans h2.E, fun e => (h1.leaves e).trans (h2.leaves e)⟩

theorem grows_append (s : PoolState) (new : List (F × ℕ)) : Grows s (s.append new) := by
  unfold PoolState.append
  split_ifs with h
  · refine ⟨by simp, by simp, fun e => ?_⟩
    simp only [Function.update_apply]
    split_ifs with he
    · subst he
      -- the new epoch's list: its old contents followed by the new leaves
      exact List.prefix_append _ _
    · exact List.prefix_refl _
  · refine ⟨by simp, by simp, fun e => ?_⟩
    simp only [Function.update_apply]
    split_ifs with he
    · subst he; exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem grows_step (P : Pool) (s s' : PoolState) (e : Event) (h : Step P s e s') : Grows s s' := by
  cases e with
  | shield inr v =>
    obtain ⟨-, -, -, -, -, rfl⟩ := h
    have := grows_append s [(cm inr v, v)]
    exact ⟨this.roots, this.E, this.leaves⟩
  | publish e =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact ⟨List.prefix_append _ _, le_rfl, fun _ => List.prefix_refl _⟩
  | rootWrite a salt r =>
    obtain ⟨-, -, rfl⟩ := h
    exact ⟨List.prefix_append _ _, le_rfl, fun _ => List.prefix_refl _⟩
  | claim r => obtain ⟨-, -, rfl⟩ := h; exact Grows.same rfl rfl rfl
  | receive v => subst h; exact Grows.same rfl rfl rfl
  | tick => subst h; exact Grows.same rfl rfl rfl
  | spend tx g =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := h
    split_ifs with h1 h2
    · have := grows_append
        { s with keys := s.keys ++ tx.nonceKeys,
                 spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
                 balance := s.balance - g } (newLeaves (settleData tx) (witOf (extOf P tx)))
      exact ⟨this.roots, this.E, this.leaves⟩
    · have := grows_append
        { s with keys := s.keys ++ tx.nonceKeys,
                 spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
                 balance := s.balance - g } (newLeaves (settleData tx) (witOf (extOf P tx)))
      exact ⟨this.roots, this.E, this.leaves⟩
    · exact Grows.same rfl rfl rfl

theorem take_of_prefix {L L' : List F} (h : L <+: L') {n : ℕ} (hn : n ≤ L.length) :
    L'.take n = L.take n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length hn]

theorem trace_mono (P : Pool) {evs evs' : List Event} {s s' : PoolState}
    (hev : evs <+: evs') (hg : Grows s s') :
    ∀ q ∈ traceQueries P evs s, q ∈ traceQueries P evs' s' := by
  intro q hq
  obtain ⟨t, rfl⟩ := hev
  obtain ⟨rt, hrt⟩ := hg.roots
  simp only [traceQueries, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.flatMap_append] at hq ⊢
  rcases hq with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl h))))
  · left; left; right
    obtain ⟨w, hw, hq⟩ := h
    exact ⟨w, by rw [← hrt]; exact List.mem_append_left _ hw, hq⟩
  · left; right
    obtain ⟨e, he, rfl⟩ := h
    exact ⟨e, lt_of_lt_of_le he hg.E, rfl⟩
  · right
    obtain ⟨e, he, hq⟩ := h
    refine ⟨e, by have := hg.E; omega, ?_⟩
    simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range] at hq ⊢
    rcases hq with (h | h | h) | ⟨n, hn, hq⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · simp at h
    · right
      have hpre := hg.leaves e
      refine ⟨n, lt_of_lt_of_le hn (by have := hpre.length_le; omega), ?_⟩
      rw [take_of_prefix hpre (by omega)]
      exact hq

/-- Consequently a bad event at a step persists to every later state of the run. -/
theorem bad_mono (P : Pool) {evs evs' : List Event} {s s' : PoolState}
    (hev : evs <+: evs') (hg : Grows s s') (ex : List Query) :
    BadEventWith P evs s ex → BadEventWith P evs' s' ex := by
  have hsub : ∀ q ∈ traceQueries P evs s ++ ex, q ∈ traceQueries P evs' s' ++ ex := by
    intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact List.mem_append_left _ (trace_mono P hev hg q h)
    · exact List.mem_append_right _ h
  rintro (⟨q1, h1, q2, h2, hc⟩ | ⟨q, hq, hd⟩ | ⟨tx, g, hm, hc⟩ | ⟨tx, g, hm, hc⟩)
  · exact Or.inl ⟨q1, hsub _ h1, q2, hsub _ h2, hc⟩
  · exact Or.inr (Or.inl ⟨q, hsub _ hq, hd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨tx, g, hev.subset hm, hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨tx, g, hev.subset hm, hc⟩))

end
end MSP

#print axioms MSP.grows_step
#print axioms MSP.bad_mono
