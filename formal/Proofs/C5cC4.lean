import Proofs.C3
import Proofs.C5a
import Sanity.Capacity
import Sanity.C4Sinks
import Mathlib.Data.List.GetD

/-! C5c and C4 from C1 and C5b, through accounting lemmas that split `owed` into
occurrences and credits. -/

namespace MSP
noncomputable section
open Classical

def occG (sp : List Occ) (vl : ℕ → List ℕ) (e i : ℕ) : ℕ :=
  if (⟨e, i⟩ : Occ) ∈ sp then 0 else (vl e).getD i 0

def occPart (s : PoolState) : ℕ :=
  ∑ e ∈ Finset.range (s.E + 1), ∑ i ∈ Finset.range (s.vals e).length, occG s.spent s.vals e i

def credSum (c : ℕ →₀ ℕ) : ℕ := c.sum fun _ v => v

theorem owed_eq (s : PoolState) : owed s = occPart s + credSum s.credit := rfl

/-! ## Generic sums -/

theorem sum_split {n : ℕ} (g g' : ℕ → ℕ) (hle : ∀ i, g' i ≤ g i) :
    ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range n, g' i + ∑ i ∈ Finset.range n, (g i - g' i) := by
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; have := hle i; omega

theorem sum_drop_one {n j : ℕ} (g g' : ℕ → ℕ) (hle : ∀ i, g' i ≤ g i) (hj : j < n) :
    ∑ i ∈ Finset.range n, g' i + (g j - g' j) ≤ ∑ i ∈ Finset.range n, g i := by
  rw [sum_split g g' hle]
  have := Finset.single_le_sum (f := fun i => g i - g' i) (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hj)
  omega

theorem sum_drop_two {n j k : ℕ} (g g' : ℕ → ℕ) (hle : ∀ i, g' i ≤ g i) (hj : j < n) (hk : k < n)
    (hjk : j ≠ k) :
    ∑ i ∈ Finset.range n, g' i + (g j - g' j) + (g k - g' k) ≤ ∑ i ∈ Finset.range n, g i := by
  rw [sum_split g g' hle]
  have hsub : ({j, k} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have := Finset.sum_le_sum_of_subset (f := fun i => g i - g' i) hsub
  rw [Finset.sum_pair hjk] at this
  omega

theorem sum_getD (L : List ℕ) : ∑ j ∈ Finset.range L.length, L.getD j 0 = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons]; omega

/-! ## Invariant: epochs above `E` hold no values -/

def ValsInv (s : PoolState) : Prop := ∀ e, s.E < e → s.vals e = []

theorem valsInv_append (s : PoolState) (new : List (F × ℕ)) (h : ValsInv s) : ValsInv (s.append new) := by
  intro e he
  unfold PoolState.append at he ⊢
  split_ifs at he ⊢ with hr
  · simp only [Function.update_apply] at he ⊢; rw [if_neg (by omega)]; exact h e (by omega)
  · simp only [Function.update_apply] at he ⊢; rw [if_neg (by omega)]; exact h e he

theorem valsInv_run (P : Pool) : ∀ evs s, Run P evs s → ValsInv s := by
  intro evs s h
  induction h with
  | nil => intro e _; rfl
  | @snoc evs s e s' _ hs ih =>
    cases e with
    | shield inr v => obtain ⟨-, -, -, -, -, rfl⟩ := hs; exact valsInv_append s _ ih
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; exact ih
    | rootWrite a salt r => obtain ⟨-, -, rfl⟩ := hs; exact ih
    | claim r => obtain ⟨-, -, rfl⟩ := hs; exact ih
    | receive v => subst hs; exact ih
    | tick => subst hs; exact ih
    | spend tx g =>
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
      have ih1 : ValsInv { s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)), balance := s.balance - g } := ih
      split_ifs
      · exact valsInv_append _ _ ih1
      · exact valsInv_append _ _ ih1
      · exact ih1

/-! ## Appending leaves adds at most their values -/

theorem inner_update (sp : List Occ) (vl : ℕ → List ℕ) (T : ℕ) (ns : List ℕ) (e : ℕ) :
    ∑ i ∈ Finset.range ((Function.update vl T (vl T ++ ns)) e).length,
        occG sp (Function.update vl T (vl T ++ ns)) e i ≤
      ∑ i ∈ Finset.range (vl e).length, occG sp vl e i + (if e = T then ns.sum else 0) := by
  by_cases he : e = T
  · subst he
    simp only [Function.update_self, List.length_append, if_true]
    rw [Finset.sum_range_add]
    apply Nat.add_le_add
    · apply le_of_eq; apply Finset.sum_congr rfl; intro i hi
      simp only [occG, Function.update_self]
      rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hi)]
    · rw [← sum_getD ns]; apply Finset.sum_le_sum; intro j _
      simp only [occG, Function.update_self]
      split_ifs
      · exact Nat.zero_le _
      · rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  · simp only [Function.update_of_ne he, he, if_false, add_zero]
    apply le_of_eq; apply Finset.sum_congr rfl; intro i _
    simp only [occG, Function.update_of_ne he]

theorem occPart_append (s : PoolState) (new : List (F × ℕ)) (hv : ValsInv s) :
    occPart (s.append new) ≤ occPart s + (new.map Prod.snd).sum := by
  unfold PoolState.append occPart
  split_ifs with hr
  · simp only
    refine le_trans (Finset.sum_le_sum fun e _ => inner_update _ _ _ _ e) ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (s.E + 1 + 1)), Finset.sum_range_succ,
      hv (s.E + 1) (by omega)]
    simp
  · simp only
    refine le_trans (Finset.sum_le_sum fun e _ => inner_update _ _ _ _ e) ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (s.E + 1))]
    simp

theorem credit_append (s : PoolState) (new : List (F × ℕ)) :
    (s.append new).credit = s.credit ∧ (s.append new).balance = s.balance ∧ (s.append new).spent = s.spent := by
  unfold PoolState.append; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem credSum_add_single (c : ℕ →₀ ℕ) (r v : ℕ) : credSum (c + Finsupp.single r v) = credSum c + v := by
  unfold credSum
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

theorem credSum_erase (c : ℕ →₀ ℕ) (r : ℕ) : credSum (c.erase r) + c r = credSum c := by
  unfold credSum
  have := Finsupp.add_sum_erase' c r (fun _ v => v) (fun _ => rfl)
  omega

theorem credit_le_credSum (c : ℕ →₀ ℕ) (r : ℕ) : c r ≤ credSum c := by
  unfold credSum Finsupp.sum
  by_cases hr : r ∈ c.support
  · exact Finset.single_le_sum (f := fun a => c a) (fun _ _ => Nat.zero_le _) hr
  · rw [Finsupp.notMem_support_iff.1 hr]; exact Nat.zero_le _


/-! ## Consuming a spend's inputs removes their values -/

theorem mem_inputsOf (sd : SettleData) (w : Witness) (k : Fin 2) (hk : w.v k ≠ 0) :
    (⟨sd.epoch, w.idx k⟩ : Occ) ∈ inputsOf sd w := by
  unfold inputsOf
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨k, hk, rfl⟩

theorem occG_mono (sp L : List Occ) (vl : ℕ → List ℕ) (e i : ℕ) : occG (sp ++ L) vl e i ≤ occG sp vl e i := by
  unfold occG; split_ifs <;> simp_all

theorem occG_consumed (sp L : List Occ) (vl : ℕ → List ℕ) (e i : ℕ) (h : (⟨e, i⟩ : Occ) ∈ L)
    (hn : (⟨e, i⟩ : Occ) ∉ sp) :
    occG sp vl e i - occG (sp ++ L) vl e i = (vl e).getD i 0 := by
  unfold occG; simp [hn, h]

theorem consume (s : PoolState) (sd : SettleData) (w : Witness) (he : sd.epoch ≤ s.E)
    (hin : ∀ k, w.v k ≠ 0 → w.idx k < (s.vals sd.epoch).length ∧
      (s.vals sd.epoch).getD (w.idx k) 0 = (w.v k).val ∧ (⟨sd.epoch, w.idx k⟩ : Occ) ∉ s.spent)
    (hdist : w.v 0 ≠ 0 → w.v 1 ≠ 0 → w.idx 0 ≠ w.idx 1) :
    (∑ e ∈ Finset.range (s.E + 1), ∑ i ∈ Finset.range (s.vals e).length,
        occG (s.spent ++ inputsOf sd w) s.vals e i) + ((w.v 0).val + (w.v 1).val) ≤ occPart s := by
  set L := inputsOf sd w
  set e0 := sd.epoch
  let g := occG s.spent s.vals e0
  let g' := occG (s.spent ++ L) s.vals e0
  have hmono : ∀ i, g' i ≤ g i := fun i => occG_mono _ _ _ _ _
  have hdrop : ∀ k, w.v k ≠ 0 → g (w.idx k) - g' (w.idx k) = (w.v k).val := by
    intro k hk
    obtain ⟨-, hv, hn⟩ := hin k hk
    rw [← hv]; exact occG_consumed _ _ _ _ _ (mem_inputsOf sd w k hk) hn
  have hz : ∀ k, w.v k = 0 → (w.v k).val = 0 := by intro k hk; rw [hk, ZMod.val_zero]
  have inner : ∑ i ∈ Finset.range (s.vals e0).length, g' i + ((w.v 0).val + (w.v 1).val) ≤
      ∑ i ∈ Finset.range (s.vals e0).length, g i := by
    by_cases h0 : w.v 0 = 0 <;> by_cases h1 : w.v 1 = 0
    · rw [hz 0 h0, hz 1 h1]; simpa using Finset.sum_le_sum fun i _ => hmono i
    · have := sum_drop_one g g' hmono (hin 1 h1).1; rw [hdrop 1 h1] at this; rw [hz 0 h0]; omega
    · have := sum_drop_one g g' hmono (hin 0 h0).1; rw [hdrop 0 h0] at this; rw [hz 1 h1]; omega
    · have := sum_drop_two g g' hmono (hin 0 h0).1 (hin 1 h1).1 (hdist h0 h1)
      rw [hdrop 0 h0, hdrop 1 h1] at this; omega
  let G := fun e => ∑ i ∈ Finset.range (s.vals e).length, occG s.spent s.vals e i
  let G' := fun e => ∑ i ∈ Finset.range (s.vals e).length, occG (s.spent ++ L) s.vals e i
  have hGm : ∀ e, G' e ≤ G e := fun e => Finset.sum_le_sum fun i _ => occG_mono _ _ _ _ _
  have := sum_drop_one G G' hGm (by omega : e0 < s.E + 1)
  have h2 : G' e0 + ((w.v 0).val + (w.v 1).val) ≤ G e0 := inner
  unfold occPart
  change ∑ e ∈ Finset.range (s.E + 1), G' e + _ ≤ ∑ e ∈ Finset.range (s.E + 1), G e
  omega

theorem newLeaves_sum (sd : SettleData) (w : Witness) :
    ((newLeaves sd w).map Prod.snd).sum ≤ (w.ov 0).val + (w.ov 1).val := by
  unfold newLeaves; split_ifs <;> simp

theorem val_cast_lt {n : ℕ} (h : n < 2 ^ 128) : ((n : F)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le h (by norm_num [p]))]

/-! ## C5c from C1 and C5b -/

theorem c5c_of (P : Pool) (hC1 : C1) (h5b : C5b P) : C5c P := by
  intro evs s h
  induction h with
  | nil => right; simp [owed, PoolState.init]
  | @snoc evs s ev s' hrun hs ih =>
    have hg := grows_step P s s' ev hs
    rcases ih with hb | hsol
    · left; exact bad_mono P (List.prefix_append _ _) hg [] hb
    rw [owed_eq] at hsol
    have hvi := valsInv_run P evs s hrun
    cases ev with
    | shield inr v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      right; rw [owed_eq]
      have h1 := occPart_append s [(cm inr v, v)] hvi
      obtain ⟨hc, -, -⟩ := credit_append s [(cm inr v, v)]
      change occPart (s.append _) + credSum (s.append _).credit ≤ s.balance + v
      rw [hc]; simp at h1; omega
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; right; exact hsol
    | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; right; exact hsol
    | claim r =>
      obtain ⟨-, hle, rfl⟩ := hs
      right; rw [owed_eq]
      change occPart s + credSum (s.credit.erase r) ≤ s.balance - s.credit r
      have := credSum_erase s.credit r
      omega
    | receive v => subst hs; right; rw [owed_eq]; change occPart s + credSum s.credit ≤ s.balance + v; omega
    | tick => subst hs; right; exact hsol
    | spend tx g =>
      by_cases hx : Satisfied (extOf P tx) ∧ publicOf (extOf P tx) = verifiedPublics tx
      swap
      · left; right; right; right; exact ⟨tx, g, by simp, hx⟩
      by_cases hcb : stmtOf (extOf P tx) = (settleData tx).stmt
      swap
      · left; right; right; left; exact ⟨tx, g, by simp, hx.1, hx.2, hcb⟩
      have hR := (hC1 _ hx.1).1
      rw [hcb] at hR
      rcases h5b evs s tx g s' hrun hs with hb | ⟨hin, hdist⟩
      · left; exact hb
      have hcap := capInv_run P evs s hrun
      obtain ⟨hacc, -, -, -, -, hmc, hgas, hs'⟩ := hs
      obtain ⟨f0, f1, f2, rest, hfr, -, -, -, -, -, hA5, -, hA7⟩ := hacc
      have hsd : settleData tx = SettleData.decode f2.data := by simp [settleData, hfr]
      rw [← hsd] at hA5 hA7
      obtain ⟨-, -, -, -, -, -, -, -, hpub, hfee, -⟩ := hA5
      set sd := settleData tx
      set w := witOf (extOf P tx)
      obtain ⟨-, -, -, -, -, -, -, hsum, hR6, -⟩ := hR
      simp only [SettleData.stmt, val_cast_lt hpub, val_cast_lt hfee] at hsum
      have hvne : ∀ k, w.v k ≠ 0 → (w.v k).val ≠ 0 := fun k hk h => hk ((ZMod.val_eq_zero _).1 h)
      have hin' : ∀ k, w.v k ≠ 0 → w.idx k < (s.vals sd.epoch).length ∧
          (s.vals sd.epoch).getD (w.idx k) 0 = (w.v k).val ∧ (⟨sd.epoch, w.idx k⟩ : Occ) ∉ s.spent := by
        intro k hk
        obtain ⟨-, -, hv, hn⟩ := hin k hk
        refine ⟨?_, hv, hn⟩
        by_contra hlt
        rw [List.getD_eq_default _ _ (by omega)] at hv
        exact hvne k hk hv.symm
      have he : sd.epoch ≤ s.E := by
        have : ∃ k, w.v k ≠ 0 := by
          by_contra hno; push_neg at hno
          rw [hno 0, hno 1, ZMod.val_zero] at hR6; omega
        obtain ⟨k, hk⟩ := this
        by_contra hlt
        have := (hin k hk).1
        rw [hcap.2 _ (by omega)] at this; simp at this
      have hcons := consume s sd w he hin' hdist
      have hnl := newLeaves_sum sd w
      set X : PoolState := { s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf sd w, balance := s.balance - g } with hXdef
      have hXo : occPart X + ((w.v 0).val + (w.v 1).val) ≤ occPart s := hcons
      have hXv : ValsInv X := hvi
      have hXb : X.balance = s.balance - g := rfl
      have hXc : X.credit = s.credit := rfl
      have h1 := occPart_append X (newLeaves sd w) hXv
      obtain ⟨hc, hb, -⟩ := credit_append X (newLeaves sd w)
      subst hs'
      right
      split_ifs with hpre hp0
      · dsimp only
        rw [owed_eq, hc, hb, hXc, hXb]
        simp only [hp0] at hsum
        omega
      · dsimp only
        rw [owed_eq]
        change occPart (X.append _) + credSum ((X.append _).credit + _) ≤ (X.append _).balance
        rw [credSum_add_single, hc, hb, hXc, hXb]
        omega
      · rw [owed_eq, hXc, hXb]
        omega

#print axioms c5c_of


/-! ## C4 from C1, C5b and C5c -/

theorem c4_of (P : Pool) (hC1 : C1) (h5b : C5b P) (h5c : C5c P) : C4 P := by
  intro evs s tx g s' hrun hs
  by_cases hB : Bounded s
  swap
  · right; left; exact hB
  have hg := grows_step P s s' _ hs
  have hpre : evs <+: evs ++ [.spend tx g] := List.prefix_append _ _
  by_cases hx : Satisfied (extOf P tx) ∧ publicOf (extOf P tx) = verifiedPublics tx
  swap
  · left; right; right; right; exact ⟨tx, g, by simp, hx⟩
  by_cases hcb : stmtOf (extOf P tx) = (settleData tx).stmt
  swap
  · left; right; right; left; exact ⟨tx, g, by simp, hx.1, hx.2, hcb⟩
  have hR := (hC1 _ hx.1).1
  rw [hcb] at hR
  rcases h5b evs s tx g s' hrun hs with hb | ⟨hin, hdist⟩
  · left; exact hb
  rcases h5c evs s hrun with hb | hsol
  · left; exact bad_mono P hpre hg [] hb
  rw [owed_eq] at hsol
  have hcap := capInv_run P evs s hrun
  obtain ⟨hacc, -, -, -, -, -, -, -⟩ := hs
  obtain ⟨f0, f1, f2, rest, hfr, -, -, -, ⟨hep, -, -⟩, -, hA5, -, -⟩ := hacc
  have hsd : settleData tx = SettleData.decode f2.data := by simp [settleData, hfr]
  rw [← hsd] at hA5 hep
  obtain ⟨hn1, hn2, hroot, hdom, hnf1, hnf2, ho1, ho2, hpub, hfee, hrcp, hauth0, hauth, hpr, hdomeq⟩ := hA5
  set sd := settleData tx
  set w := witOf (extOf P tx)
  -- sinks: a collision with the hardcoded sink queries is a bad event
  have hq := sink_queries_in_trace P (evs ++ [.spend tx g]) s'
  have hoq : Query.h3 2 (w.oi 1) (w.ov 1) ∈ traceQueries P (evs ++ [.spend tx g]) s' ∧
      Query.h3 2 (w.oi 0) (w.ov 0) ∈ traceQueries P (evs ++ [.spend tx g]) s' := by
    constructor <;> simp [traceQueries, eventQueries, witnessQueries, w]
  by_cases hc1 : (Query.h3 2 (w.oi 1) (w.ov 1)).collide (Query.h3 2 1 0)
  · left; left; exact ⟨_, List.mem_append_left _ hoq.1, _, List.mem_append_left _ hq.1, hc1⟩
  by_cases hc0 : (Query.h3 2 (w.oi 0) (w.ov 0)).collide (Query.h3 2 2 0)
  · left; left; exact ⟨_, List.mem_append_left _ hoq.2, _, List.mem_append_left _ hq.2, hc0⟩
  have hs0 := o2_ne_sink0 sd.stmt w hR hc1
  have hs1 := o1_ne_sink1 sd.stmt w hR hc0
  have hR' := hR
  obtain ⟨-, -, -, -, -, -, -, hsum, hR6, -, -, hR8, -⟩ := hR'
  simp only [SettleData.stmt, val_cast_lt hpub, val_cast_lt hfee] at hsum
  -- the inputs
  have hvne : ∀ k, w.v k ≠ 0 → (w.v k).val ≠ 0 := fun k hk h => hk ((ZMod.val_eq_zero _).1 h)
  have hin' : ∀ k, w.v k ≠ 0 → w.idx k < (s.vals sd.epoch).length ∧
      (s.vals sd.epoch).getD (w.idx k) 0 = (w.v k).val ∧ (⟨sd.epoch, w.idx k⟩ : Occ) ∉ s.spent := by
    intro k hk
    obtain ⟨-, -, hv, hn⟩ := hin k hk
    refine ⟨?_, hv, hn⟩
    by_contra hlt
    rw [List.getD_eq_default _ _ (by omega)] at hv
    exact hvne k hk hv.symm
  have he : sd.epoch ≤ s.E := by
    have : ∃ k, w.v k ≠ 0 := by
      by_contra hno; push_neg at hno
      rw [hno 0, hno 1, ZMod.val_zero] at hR6; omega
    obtain ⟨k, hk⟩ := this
    by_contra hlt
    have := (hin k hk).1
    rw [hcap.2 _ (by omega)] at this; simp at this
  have hcons := consume s sd w he hin' hdist
  have hcr := credit_le_credSum s.credit sd.rcp
  right; right
  refine ⟨hep, hrcp, hauth, hn1, hn2, by omega, hdomeq, he, hroot, hdom, hnf1, hnf2, ho1, ho2, hpub, hfee, hpr,
    ?_, ?_, ?_, fun _ => hB.1, fun _ => ?_⟩
  · intro h; apply hR8; simp [SettleData.stmt, h]
  · intro h; apply hs1; simp only [SettleData.stmt]; rw [h, ZMod.natCast_zmod_val]
  · intro h; apply hs0; simp only [SettleData.stmt]; rw [h, ZMod.natCast_zmod_val]
  · have := hB.2; omega

#print axioms c4_of

end
end MSP
