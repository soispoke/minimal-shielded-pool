import Spec

/-! `historyEvents` of a slot-nondecreasing write log by addresses
other than the pool, with root words below `2 ^ 256`, is a model run ending at
`slot`, provided every logged slot is at most `slot`. Its roots are the log's
entries with their own slots. -/

namespace MSP
noncomputable section
open Classical

def histStep (acc : List Event × ℕ) (w : ℕ × ℕ × ℕ × ℕ) : List Event × ℕ :=
  (acc.1 ++ List.replicate (w.2.2.1 - acc.2) Event.tick ++ [Event.rootWrite w.1 w.2.1 w.2.2.2],
   max acc.2 w.2.2.1)

theorem historyEvents_eq (log : List (ℕ × ℕ × ℕ × ℕ)) (slot : ℕ) :
    historyEvents log slot =
      (log.foldl histStep ([], 0)).1 ++ List.replicate (slot - (log.foldl histStep ([], 0)).2) Event.tick := rfl

def entryOf (w : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (K (addr20 w.1 ++ u256 w.2.1), w.2.2.1, w.2.2.2)

theorem run_ticks (P : Pool) : ∀ (k : ℕ) (evs : List Event) (s : PoolState), Run P evs s →
    Run P (evs ++ List.replicate k Event.tick) { s with slot := s.slot + k } := by
  intro k
  induction k with
  | zero => intro evs s h; simpa using h
  | succ k ih =>
    intro evs s h
    have := Run.snoc (e := Event.tick) (ih evs s h) (rfl)
    rw [List.append_assoc, ← List.replicate_succ'] at this
    simpa [Nat.add_assoc] using this

theorem hist_fold (P : Pool) (B : ℕ) :
    ∀ (log : List (ℕ × ℕ × ℕ × ℕ)) (evs0 : List Event) (cur : ℕ) (s0 : PoolState),
      Run P evs0 s0 → s0.slot = cur → cur ≤ B →
      (∀ w ∈ log, cur ≤ w.2.2.1 ∧ w.2.2.1 ≤ B ∧ addr20 w.1 ≠ addr20 P.A ∧ w.2.2.2 < 2 ^ 256) →
      log.Pairwise (fun a b => a.2.2.1 ≤ b.2.2.1) →
      ∃ s, Run P (log.foldl histStep (evs0, cur)).1 s ∧ s.slot = (log.foldl histStep (evs0, cur)).2 ∧
        (log.foldl histStep (evs0, cur)).2 ≤ B ∧ s.roots = s0.roots ++ log.map entryOf := by
  intro log
  induction log with
  | nil => intro evs0 cur s0 h hs hB _ _; exact ⟨s0, h, hs, hB, by simp⟩
  | cons w rest ih =>
    intro evs0 cur s0 h hs hB hw hp
    obtain ⟨hc, hwB, ha, hr⟩ := hw w (by simp)
    rw [List.pairwise_cons] at hp
    have h1 := run_ticks P (w.2.2.1 - cur) evs0 s0 h
    set s1 := { s0 with slot := s0.slot + (w.2.2.1 - cur) }
    have hs1 : s1.slot = w.2.2.1 := by simp [s1, hs]; omega
    have h2 := Run.snoc (e := Event.rootWrite w.1 w.2.1 w.2.2.2) h1
      (s' := { s1 with roots := s1.roots ++ [(K (addr20 w.1 ++ u256 w.2.1), s1.slot, w.2.2.2)] })
      ⟨ha, hr, rfl⟩
    simp only [List.foldl_cons]
    have hmax : max cur w.2.2.1 = w.2.2.1 := by omega
    obtain ⟨s, hrun, hsl, hle, hroots⟩ := ih _ w.2.2.1 _ h2 hs1 hwB
      (fun w' hw' => ⟨hp.1 w' hw', (hw w' (by simp [hw'])).2⟩) hp.2
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · simpa [histStep, hmax] using hrun
    · simpa [histStep, hmax] using hsl
    · simpa [histStep, hmax] using hle
    · rw [hroots]; simp only [s1, entryOf, List.map_cons, List.append_assoc, List.singleton_append]
      rw [show s0.slot + (w.2.2.1 - cur) = w.2.2.1 by omega]

/-- The history is a run ending at `slot`, with the log's entries as roots. -/
theorem historyEvents_run (P : Pool) (log : List (ℕ × ℕ × ℕ × ℕ)) (slot : ℕ)
    (hw : ∀ w ∈ log, w.2.2.1 ≤ slot ∧ addr20 w.1 ≠ addr20 P.A ∧ w.2.2.2 < 2 ^ 256)
    (hp : log.Pairwise (fun a b => a.2.2.1 ≤ b.2.2.1)) :
    ∃ s, Run P (historyEvents log slot) s ∧ s.slot = slot ∧ s.roots = log.map entryOf := by
  obtain ⟨s, hrun, hsl, hle, hroots⟩ := hist_fold P slot log [] 0 PoolState.init Run.nil rfl (Nat.zero_le _)
    (fun w h => ⟨Nat.zero_le _, hw w h⟩) hp
  have := run_ticks P (slot - (log.foldl histStep ([], 0)).2) _ s hrun
  refine ⟨_, by rw [historyEvents_eq]; exact this, by simp [hsl]; omega, by simpa [PoolState.init] using hroots⟩

#print axioms historyEvents_run

end
end MSP
