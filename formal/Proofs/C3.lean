import Sanity.Mono

/-! C5e outright, and C3 from C1 (all four conjuncts), via C5e's invariant. -/

namespace MSP
noncomputable section
open Classical

theorem be_length (k n : ℕ) : (be k n).length = k := by simp [be]

theorem be_succ (k n : ℕ) : be (k + 1) n = UInt8.ofNat (n / 256 ^ k % 256) :: be k n := by
  simp [be, List.range_succ]

theorem be_mod (k n m : ℕ) (h : be k n = be k m) : n % 256 ^ k = m % 256 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [be_succ, be_succ] at h
    obtain ⟨hd, tl⟩ := List.cons.inj h
    have hd' : n / 256 ^ k % 256 = m / 256 ^ k % 256 := by
      have := congrArg UInt8.toNat hd
      simpa [UInt8.toNat_ofNat, Nat.mod_mod] using this
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih tl, hd']

theorem u256_inj {n m : ℕ} (hn : n < 2 ^ 256) (hm : m < 2 ^ 256) (h : u256 n = u256 m) : n = m := by
  have := be_mod 32 n m h
  rw [show (256 : ℕ) ^ 32 = 2 ^ 256 by norm_num, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact this

theorem p_lt : p < 2 ^ 256 := by norm_num [p]

theorem bad_of_extra (P : Pool) (evs : List Event) (s : PoolState) (ex : List Query)
    (h : ∀ q ∈ ex, q ∈ traceQueries P evs s) : BadEventWith P evs s ex → BadEvent P evs s := by
  have hsub : ∀ q ∈ traceQueries P evs s ++ ex, q ∈ traceQueries P evs s ++ [] := by
    intro q hq
    rcases List.mem_append.1 hq with h' | h'
    · simpa using h'
    · simpa using h q h'
  rintro (⟨q1, h1, q2, h2, hc⟩ | ⟨q, hq, hd⟩ | hc | hc)
  · exact Or.inl ⟨q1, hsub _ h1, q2, hsub _ h2, hc⟩
  · exact Or.inr (Or.inl ⟨q, hsub _ hq, hd⟩)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hc))

/-! ## The finalRoot invariant -/

def FinInv (s : PoolState) : Prop := ∀ e < s.E, s.finalRoot e = TR (s.leaves e)

theorem finInv_append (s : PoolState) (new : List (F × ℕ)) (h : FinInv s) : FinInv (s.append new) := by
  intro e he
  unfold PoolState.append at he ⊢
  by_cases hr : rollsOver s new.length
  · simp only [hr, if_true, Function.update_apply] at he ⊢
    rw [if_neg (by omega : ¬ e = s.E + 1)]
    by_cases hE : e = s.E
    · subst hE; simp
    · rw [if_neg hE]; exact h e (by omega)
  · simp only [hr, if_false, Function.update_apply] at he ⊢
    rw [if_neg (by omega : ¬ e = s.E)]; exact h e he

theorem finInv_run (P : Pool) : ∀ evs s, Run P evs s → FinInv s := by
  intro evs s h
  induction h with
  | nil => intro e he; simp [PoolState.init] at he
  | @snoc evs s e s' _ hs ih =>
    cases e with
    | shield inr v => obtain ⟨-, -, -, -, -, rfl⟩ := hs; exact finInv_append s _ ih
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact ih
    | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; exact ih
    | claim r0 => obtain ⟨-, -, rfl⟩ := hs; exact ih
    | receive v => subst hs; exact ih
    | tick => subst hs; exact ih
    | spend tx g =>
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
      have ih1 : FinInv { s with keys := s.keys ++ tx.nonceKeys,
                                  spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
                                  balance := s.balance - g } := ih
      split_ifs
      · exact finInv_append _ _ ih1
      · exact finInv_append _ _ ih1
      · exact ih1

/-! ## C5e -/

theorem msg_ne_addr {a b : ℕ} (x y : ℕ) (h : addr20 a ≠ addr20 b) : addr20 a ++ u256 x ≠ addr20 b ++ u256 y := by
  intro he
  exact h (List.append_inj he (by simp [addr20, be_length])).1

theorem msg_ne_epoch (A : ℕ) {e e' : ℕ} (he : e < 2 ^ 64) (he' : e' < 2 ^ 64) (hne : e' ≠ e) :
    addr20 A ++ u256 e' ≠ addr20 A ++ u256 e := by
  intro h
  exact hne (u256_inj (by omega) (by omega) (List.append_cancel_left h))

theorem c5e (P : Pool) : C5e P := by
  intro evs s h
  induction h with
  | nil => intro r hr; simp [PoolState.init] at hr
  | @snoc evs s ev s' hrun hs ih =>
    have hg := grows_step P s s' ev hs
    have hpre : evs <+: evs ++ [ev] := List.prefix_append _ _
    -- old roots carry over
    have old : ∀ r ∈ s.roots, ∀ e < 2 ^ 64, r.1 = sourceId P.A e →
        BadEventWith P (evs ++ [ev]) s' [.keccak (addr20 P.A ++ u256 e)] ∨
        (e ≤ s'.E ∧ ∃ n ≤ (s'.leaves e).length, r.2.2 = (TR ((s'.leaves e).take n)).val) := by
      intro r hr e he hre
      rcases ih r hr e he hre with hb | ⟨hle, n, hn, hrt⟩
      · exact Or.inl (bad_mono P hpre hg _ hb)
      · right
        refine ⟨hle.trans hg.E, n, hn.trans (hg.leaves e).length_le, ?_⟩
        rw [take_of_prefix (hg.leaves e) hn]; exact hrt
    have finv := finInv_run P evs s hrun
    cases ev with
    | publish e' =>
      obtain ⟨he'64, he'E, hr0, rfl⟩ := hs
      intro r hr e he hre
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact old r hr e he hre
      · by_cases hee : e' = e
        · subst hee
          right
          refine ⟨he'E, (s.leaves e').length, le_rfl, ?_⟩
          simp only [List.take_length]
          split_ifs with hE
          · subst hE; rfl
          · rw [finv e' (lt_of_le_of_ne he'E hE)]
        · left; left
          refine ⟨.keccak (addr20 P.A ++ u256 e'), ?_, .keccak (addr20 P.A ++ u256 e), by simp,
            msg_ne_epoch P.A he he'64 hee, hre⟩
          apply List.mem_append_left
          simp only [traceQueries, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
          right
          exact ⟨e', by simp; omega, Or.inl (Or.inr (Or.inl rfl))⟩
    | rootWrite a salt x =>
      obtain ⟨ha, hx, rfl⟩ := hs
      intro r hr e he hre
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact old r hr e he hre
      · left; left
        refine ⟨.keccak (addr20 a ++ u256 salt), ?_, .keccak (addr20 P.A ++ u256 e), by simp,
          msg_ne_addr salt e ha, hre⟩
        apply List.mem_append_left
        simp [traceQueries, eventQueries]
    | shield inr v =>
      have hroots : s'.roots = s.roots := by
        obtain ⟨-, -, -, -, -, rfl⟩ := hs; unfold PoolState.append; split_ifs <;> rfl
      intro r hr; rw [hroots] at hr; exact old r hr
    | claim r0 =>
      obtain ⟨-, -, rfl⟩ := hs; exact old
    | receive v => subst hs; exact old
    | tick => subst hs; exact old
    | spend tx g =>
      have hroots : s'.roots = s.roots := by
        obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
        split_ifs <;> first | rfl | (unfold PoolState.append; split_ifs <;> rfl)
      intro r hr; rw [hroots] at hr; exact old r hr

/-! ## C3 -/

theorem c3 (P : Pool) (hC1 : C1) : C3 P := by
  intro evs s tx g s' hrun hs
  have hg := grows_step P s s' _ hs
  have hpre : evs <+: evs ++ [.spend tx g] := List.prefix_append _ _
  -- extraction and compression
  by_cases hx : Satisfied (extOf P tx) ∧ publicOf (extOf P tx) = verifiedPublics tx
  swap
  · left; right; right; right; exact ⟨tx, g, by simp, hx⟩
  by_cases hcb : stmtOf (extOf P tx) = (settleData tx).stmt
  swap
  · left; right; right; left; exact ⟨tx, g, by simp, hx.1, hx.2, hcb⟩
  have hR := (hC1 _ hx.1).1
  rw [hcb] at hR
  obtain ⟨hacc, hkw, -, -, ⟨hlw, -, -⟩, -, -, -⟩ := hs
  obtain ⟨f0, f1, f2, rest, hfr, -, -, ⟨-, hlen, hkh⟩, ⟨hep, -, -⟩, ⟨sg, hsg, hsch, hmsg, hsig⟩, hA5, -, -⟩ := hacc
  have hsd : settleData tx = SettleData.decode f2.data := by simp [settleData, hfr]
  rw [← hsd] at hkh hA5 hep hsig
  obtain ⟨-, -, -, -, hn1, hn2, -⟩ := hA5
  set sd := settleData tx with hsd_def
  -- the root: from lastWrite and C5e
  have hw : ∃ w ∈ s.roots, w.1 = sourceId P.A sd.epoch ∧ w.2.2 = sd.root := by
    unfold lastWrite at hlw
    obtain ⟨w, hw1, hw2⟩ := Option.map_eq_some_iff.mp hlw
    have hmem := List.mem_of_getLast? hw1
    rw [List.mem_filter] at hmem
    simp only [decide_eq_true_eq] at hmem
    exact ⟨w, hmem.1, hmem.2.1, hw2⟩
  obtain ⟨w, hwm, hw1, hw2⟩ := hw
  have hext : Query.keccak (addr20 P.A ++ u256 sd.epoch) ∈ traceQueries P (evs ++ [.spend tx g]) s' := by
    simp [traceQueries, eventQueries, sd]
  rcases c5e P evs s hrun w hwm sd.epoch hep hw1 with hb | ⟨-, n, hn, hroot⟩
  · left
    exact bad_of_extra P _ _ _ (by simpa using hext) (bad_mono P hpre hg _ hb)
  -- the keys
  set m1 := u256 tx.nonceKeys.length ++ tx.nonceKeys.flatMap u256
  set m2 := u256 2 ++ u256 (min sd.nf1 sd.nf2) ++ u256 (max sd.nf1 sd.nf2)
  have hq1 : Query.keccak m1 ∈ traceQueries P (evs ++ [.spend tx g]) s' := by
    simp [traceQueries, eventQueries, m1]
  have hq2 : Query.keccak m2 ∈ traceQueries P (evs ++ [.spend tx g]) s' := by
    simp [traceQueries, eventQueries, m2, sd]
  by_cases hm : m1 = m2
  swap
  · left; left
    refine ⟨.keccak m1, List.mem_append_left _ hq1, .keccak m2, List.mem_append_left _ hq2, hm, ?_⟩
    simpa [keysHash, m1, m2] using hkh
  right
  refine ⟨hR, ?_, ⟨n, hn, ?_⟩, ⟨sg, by simp [hsg], hsch, hmsg, hsig⟩⟩
  · obtain ⟨k0, k1, hk⟩ := List.length_eq_two.mp hlen
    have hk0 : k0 < 2 ^ 256 := hkw k0 (by simp [hk])
    have hk1 : k1 < 2 ^ 256 := hkw k1 (by simp [hk])
    simp only [m1, m2, hk, List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] at hm
    have hm' := List.append_cancel_left hm
    obtain ⟨h0, h1⟩ := List.append_inj hm' (by simp [u256, be_length])
    have hmin : min sd.nf1 sd.nf2 < 2 ^ 256 := lt_of_le_of_lt (min_le_left _ _) (hn1.trans p_lt)
    have hmax : max sd.nf1 sd.nf2 < 2 ^ 256 := max_lt (hn1.trans p_lt) (hn2.trans p_lt)
    rw [hk, u256_inj hk0 hmin h0, u256_inj hk1 hmax h1]
  · rw [← hw2, hroot, ZMod.natCast_zmod_val]

end
end MSP
