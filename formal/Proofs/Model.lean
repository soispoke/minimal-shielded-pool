import Proofs.C5d
import Proofs.C5b
import Sanity.SpendableR

/-! C5g, C5h and spendability from C1, and the model half of the main theorem. -/

namespace MSP
noncomputable section
open Classical

theorem bad_with_sub (P : Pool) (evs : List Event) (s : PoolState) (ex ex' : List Query)
    (h : ∀ q ∈ ex, q ∈ ex') : BadEventWith P evs s ex → BadEventWith P evs s ex' := by
  have hsub : ∀ q ∈ traceQueries P evs s ++ ex, q ∈ traceQueries P evs s ++ ex' := by
    intro q hq
    rcases List.mem_append.1 hq with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (h q h')
  rintro (⟨q1, h1, q2, h2, hc⟩ | ⟨q, hq, hd⟩ | hc | hc)
  · exact Or.inl ⟨q1, hsub _ h1, q2, hsub _ h2, hc⟩
  · exact Or.inr (Or.inl ⟨q, hsub _ hq, hd⟩)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hc))

theorem clean_or_bad (P : Pool) (evs : List Event) (s : PoolState) (ex : List Query) :
    BadEventWith P evs s ex ∨
      (NoColl (traceQueries P evs s ++ ex) ∧ ∀ q ∈ traceQueries P evs s ++ ex, ¬ q.degenerate) := by
  by_cases hNC : NoColl (traceQueries P evs s ++ ex)
  · by_cases hND : ∀ q ∈ traceQueries P evs s ++ ex, ¬ q.degenerate
    · exact Or.inr ⟨hNC, hND⟩
    · left; right; left; push Not at hND; exact hND
  · left; left; unfold NoColl at hNC; push Not at hNC; exact hNC

structure GoodSpend (P : Pool) (tx : FrameTx) : Prop where
  st : stmtOf (extOf P tx) = stmtOfTx tx
  R : R (stmtOfTx tx) (witOf (extOf P tx))
  dom : (settleData tx).domain = (D P.c P.A (settleData tx).epoch).val
  n1 : (settleData tx).nf1 < p
  n2 : (settleData tx).nf2 < p
  keys : tx.nonceKeys = [min (settleData tx).nf1 (settleData tx).nf2,
                         max (settleData tx).nf1 (settleData tx).nf2]

theorem acc_facts (P : Pool) (tx : FrameTx) (hacc : Acc P.A P.c P.verifies 1 tx) :
    (settleData tx).domain = (D P.c P.A (settleData tx).epoch).val ∧
      (settleData tx).nf1 < p ∧ (settleData tx).nf2 < p := by
  obtain ⟨f0, f1, f2, rest, hfr, -, -, -, -, -, hA5, -, -⟩ := hacc
  have hsd : settleData tx = SettleData.decode f2.data := by simp [settleData, hfr]
  rw [← hsd] at hA5
  obtain ⟨-, -, -, -, hn1, hn2, -, -, -, -, -, -, -, -, hdom⟩ := hA5
  exact ⟨hdom, hn1, hn2⟩

theorem good_spend (P : Pool) (hC1 : C1) (evs : List Event) (s : PoolState) (tx : FrameTx) (g : ℕ)
    (s' : PoolState) (hrun : Run P evs s) (hs : Step P s (.spend tx g) s') :
    BadEvent P (evs ++ [.spend tx g]) s' ∨ GoodSpend P tx := by
  by_cases hx : Satisfied (extOf P tx) ∧ publicOf (extOf P tx) = verifiedPublics tx
  swap
  · left; right; right; right; exact ⟨tx, g, by simp, hx⟩
  by_cases hcb : stmtOf (extOf P tx) = (settleData tx).stmt
  swap
  · left; right; right; left; exact ⟨tx, g, by simp, hx.1, hx.2, hcb⟩
  rcases c3 P hC1 evs s tx g s' hrun hs with hb | ⟨hR, hkeys, -, -⟩
  · left; exact hb
  obtain ⟨hd, h1, h2⟩ := acc_facts P tx hs.1
  exact Or.inr ⟨hcb, hR, hd, h1, h2, hkeys⟩

theorem stmt_d (P : Pool) (tx : FrameTx) (hG : GoodSpend P tx) :
    (stmtOf (extOf P tx)).d = D P.c P.A (settleData tx).epoch := by
  rw [hG.st]; show ((settleData tx).domain : F) = _; rw [hG.dom, ZMod.natCast_zmod_val]

theorem mem_wq_nf (x : Statement) (w : Witness) (k : Fin 2) :
    Query.h2 x.d (w.sk k) ∈ witnessQueries x w ∧
    Query.h2 (w.leaf k) (w.idx k : F) ∈ witnessQueries x w ∧
    Query.h3 4 (nfKey x.d (w.sk k)) (H2 (w.leaf k) (w.idx k : F)) ∈ witnessQueries x w := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold witnessQueries
    apply List.mem_append_left
    rw [List.mem_flatMap]
    exact ⟨k, List.mem_finRange k, by simp⟩

theorem cast_inj_small {a b : ℕ} (ha : a < 2 ^ DEPTH) (hb : b < 2 ^ DEPTH) (h : (a : F) = (b : F)) :
    a = b := by
  have hp : 2 ^ DEPTH < p := by norm_num [DEPTH, p]
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (ha.trans hp),
    Nat.mod_eq_of_lt (hb.trans hp)] at this

/-- A key a good spend consumed that equals `nf (D e) sk leaf i` pins the spend's
input: same epoch, index, leaf and key, or the queries collide. -/
theorem key_match (P : Pool) (T : List Query) (hNC : NoColl T) (tx : FrameTx) (hG : GoodSpend P tx)
    (hwq : ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)), q ∈ T)
    (hdom : Query.dom P.c P.A (settleData tx).epoch ∈ T)
    (e i : ℕ) (sk leaf : F) (hi : i < 2 ^ DEPTH)
    (o3 : Query.h3 4 (nfKey (D P.c P.A e) sk) (H2 leaf (i : F)) ∈ T)
    (o2 : Query.h2 (D P.c P.A e) sk ∈ T) (o1 : Query.h2 leaf (i : F) ∈ T)
    (od : Query.dom P.c P.A e ∈ T)
    (hmem : (nf (D P.c P.A e) sk leaf i).val ∈ tx.nonceKeys) :
    ∃ k, e = (settleData tx).epoch ∧ i = (witOf (extOf P tx)).idx k ∧
      leaf = (witOf (extOf P tx)).leaf k ∧ sk = (witOf (extOf P tx)).sk k := by
  have hd := stmt_d P tx hG
  obtain ⟨hR1, h2a, h2b, -⟩ := hG.R
  set X := nf (D P.c P.A e) sk leaf i with hX
  set w := witOf (extOf P tx) with hw
  set sd := settleData tx with hsd
  have hor : X.val = sd.nf1 ∨ X.val = sd.nf2 := by
    rw [hG.keys] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> rcases le_total sd.nf1 sd.nf2 with hl | hl
    · left; rw [h, min_eq_left hl]
    · right; rw [h, min_eq_right hl]
    · right; rw [h, max_eq_right hl]
    · left; rw [h, max_eq_left hl]
  have hk : ∃ k : Fin 2, X = nf (stmtOf (extOf P tx)).d (w.sk k) (w.leaf k) (w.idx k) := by
    rw [hG.st]
    rcases hor with h | h
    · exact ⟨0, by rw [← ZMod.natCast_zmod_val X, h]; exact h2a⟩
    · exact ⟨1, by rw [← ZMod.natCast_zmod_val X, h]; exact h2b⟩
  obtain ⟨k, hXk⟩ := hk
  obtain ⟨w2, w1, w3⟩ := mem_wq_nf (stmtOf (extOf P tx)) w k
  obtain ⟨-, hkey, hin⟩ := h3_inj hNC o3 (hwq _ w3) hXk
  obtain ⟨hde, hsk⟩ := h2_inj hNC o2 (hwq _ w2) hkey
  obtain ⟨hleaf, hidx⟩ := h2_inj hNC o1 (hwq _ w1) hin
  have he : e = sd.epoch := by
    by_contra hne
    rw [hd] at hde
    exact hNC _ od _ hdom ⟨by simp [hne], hde⟩
  exact ⟨k, he, cast_inj_small hi (hR1 k) hidx, hleaf, hsk⟩

/-- A leaf created with a positive value is no zero-value input. -/
theorem input_nonzero (T : List Query) (hNC : NoColl T) (w : Witness) (k : Fin 2) (x : Statement)
    (hwq : ∀ q ∈ witnessQueries x w, q ∈ T) (inr : F) (val : ℕ) (hval : 0 < val)
    (hval' : val < 2 ^ 128) (hq : Query.h3 2 inr (val : F) ∈ T) (hleaf : cm inr (val : F) = w.leaf k) :
    w.v k ≠ 0 := by
  intro hv
  obtain ⟨-, -, w3, -⟩ := mem_witnessQueries_k x w k
  obtain ⟨-, -, h⟩ := h3_inj hNC hq (hwq _ w3) hleaf
  rw [hv] at h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hval' (by norm_num [p])), ZMod.val_zero] at this
  omega

theorem leaf_facts (P : Pool) (hC1 : C1) (evs : List Event) (s : PoolState) (hrun : Run P evs s) :
    BadEvent P evs s ∨ ∀ e i, i < (s.leaves e).length → i < 2 ^ DEPTH ∧
      ∃ inr, ∃ val : ℕ, 0 < val ∧ val < 2 ^ 128 ∧ (s.leaves e).getD i 0 = cm inr (val : F) ∧
        Query.h3 2 inr (val : F) ∈ traceQueries P evs s := by
  rcases binv_run P hC1 evs s hrun with hb | hinv
  · exact Or.inl hb
  rcases c5a P hC1 evs s hrun with hb | h5a
  · exact Or.inl hb
  right
  intro e i hi
  have hcap := capInv_run P evs s hrun
  refine ⟨lt_of_lt_of_le hi (hcap.1 e), ?_⟩
  obtain ⟨hv128, inr, hc, hq⟩ := forall₂_getD (hinv.1 e) hi
  obtain ⟨-, hpos, -⟩ := h5a e i hi
  exact ⟨inr, _, hpos, hv128, hc, Qe_in_trace P evs s _ hq⟩

theorem spend_keys_spent (P : Pool) (s s' : PoolState) (tx : FrameTx) (g : ℕ)
    (hs : Step P s (.spend tx g) s') :
    s'.keys = s.keys ++ tx.nonceKeys ∧
      s'.spent = s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)) := by
  obtain ⟨-, -, -, -, -, -, -, hs'⟩ := hs
  subst hs'
  obtain ⟨hk, hsp⟩ := append_keys_spent
    ({ s with keys := s.keys ++ tx.nonceKeys,
              spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
              balance := s.balance - g } : PoolState) (newLeaves (settleData tx) (witOf (extOf P tx)))
  split_ifs
  · exact ⟨hk, hsp⟩
  · exact ⟨hk, hsp⟩
  · exact ⟨rfl, rfl⟩

/-- Every consumed key comes from a good spend of the run whose inputs are spent. -/
def KInv (P : Pool) (evs : List Event) (s : PoolState) : Prop :=
  ∀ key ∈ s.keys, ∃ tx g, Event.spend tx g ∈ evs ∧ GoodSpend P tx ∧ key ∈ tx.nonceKeys ∧
    ∀ o ∈ inputsOf (settleData tx) (witOf (extOf P tx)), o ∈ s.spent

theorem kinv_run (P : Pool) (hC1 : C1) : ∀ evs s, Run P evs s → BadEvent P evs s ∨ KInv P evs s := by
  intro evs s h
  induction h with
  | nil => right; intro key hk; simp [PoolState.init] at hk
  | @snoc evs s ev s' hrun hs ih =>
    have hg := grows_step P s s' ev hs
    rcases ih with hb | hinv
    · left; exact bad_mono P (List.prefix_append _ _) hg [] hb
    have same : s'.keys = s.keys → s'.spent = s.spent → KInv P (evs ++ [ev]) s' := by
      intro h1 h2 key hk
      rw [h1] at hk
      obtain ⟨tx, g, hm, hG, hkm, hsub⟩ := hinv key hk
      exact ⟨tx, g, List.mem_append_left _ hm, hG, hkm, fun o ho => by rw [h2]; exact hsub o ho⟩
    cases ev with
    | shield inr v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      obtain ⟨hk, hsp⟩ := append_keys_spent s [(cm inr v, v)]
      right; exact same hk hsp
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; right; exact same rfl rfl
    | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; right; exact same rfl rfl
    | claim r => obtain ⟨-, -, rfl⟩ := hs; right; exact same rfl rfl
    | receive v => subst hs; right; exact same rfl rfl
    | tick => subst hs; right; exact same rfl rfl
    | spend tx g =>
      rcases good_spend P hC1 evs s tx g s' hrun hs with hb | hG
      · left; exact hb
      right
      obtain ⟨hk, hsp⟩ := spend_keys_spent P s s' tx g hs
      intro key hkey
      rw [hk] at hkey
      rcases List.mem_append.1 hkey with h | h
      · obtain ⟨tx', g', hm, hG', hkm, hsub⟩ := hinv key h
        exact ⟨tx', g', List.mem_append_left _ hm, hG', hkm,
          fun o ho => by rw [hsp]; exact List.mem_append_left _ (hsub o ho)⟩
      · exact ⟨tx, g, by simp, hG, h, fun o ho => by rw [hsp]; exact List.mem_append_right _ ho⟩

theorem opening_mem (P : Pool) (e i : ℕ) (sk ρ v : F) :
    Query.h3 4 (nfKey (D P.c P.A e) sk) (H2 (cm (inner sk ρ) v) (i : F)) ∈ openingQueries P e i sk ρ v ∧
    Query.h2 (D P.c P.A e) sk ∈ openingQueries P e i sk ρ v ∧
    Query.h2 (cm (inner sk ρ) v) (i : F) ∈ openingQueries P e i sk ρ v ∧
    Query.dom P.c P.A e ∈ openingQueries P e i sk ρ v ∧
    Query.h3 2 (inner sk ρ) v ∈ openingQueries P e i sk ρ v := by
  simp [openingQueries]

/-! ## C5g -/

theorem c5g (P : Pool) (hC1 : C1) : C5g P := by
  intro evs s tx g s' hrun hs o sk ρ v hi hleaf hmem
  have hg := grows_step P s s' _ hs
  have hpre : evs <+: evs ++ [.spend tx g] := List.prefix_append _ _
  set ex := openingQueries P o.e o.i sk ρ v with hex
  rcases leaf_facts P hC1 evs s hrun with hb | hlf
  · left; exact bad_with_of_bad P _ _ _ (bad_mono P hpre hg [] hb)
  rcases good_spend P hC1 evs s tx g s' hrun hs with hb | hG
  · left; exact bad_with_of_bad P _ _ _ hb
  rcases clean_or_bad P (evs ++ [.spend tx g]) s' ex with hb | ⟨hNC, -⟩
  · left; exact hb
  right
  set T := traceQueries P (evs ++ [.spend tx g]) s' ++ ex with hT
  obtain ⟨hi20, inr, val, hpos, h128, hc, hq⟩ := hlf o.e o.i hi
  have hwq : ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)), q ∈ T := fun q hq =>
    List.mem_append_left _ (spend_wq_in_trace P evs tx g s' q hq)
  have hdom : Query.dom P.c P.A (settleData tx).epoch ∈ T :=
    List.mem_append_left _ (by simp [traceQueries, eventQueries])
  obtain ⟨o3, o2, o1, od, -⟩ := opening_mem P o.e o.i sk ρ v
  rw [hleaf] at hmem
  obtain ⟨k, he, hidx, hlk, -⟩ := key_match P T hNC tx hG hwq hdom o.e o.i sk (cm (inner sk ρ) v) hi20
    (List.mem_append_right _ o3) (List.mem_append_right _ o2) (List.mem_append_right _ o1)
    (List.mem_append_right _ od) hmem
  have hq' : Query.h3 2 inr (val : F) ∈ T := List.mem_append_left _ (trace_mono P hpre hg _ hq)
  have hvk := input_nonzero T hNC _ k _ hwq inr val hpos h128 hq' (hc.symm.trans (hleaf.trans hlk))
  have ho : o = ⟨(settleData tx).epoch, (witOf (extOf P tx)).idx k⟩ := by
    cases o; simp only [Occ.mk.injEq]; exact ⟨he, hidx⟩
  rw [ho]; exact mem_inputsOf _ _ k hvk

/-! ## C5h -/

theorem c5h (P : Pool) (hC1 : C1) : C5h P := by
  intro evs s hrun o sk ρ v hi hns hleaf
  set ex := openingQueries P o.e o.i sk ρ v with hex
  rcases leaf_facts P hC1 evs s hrun with hb | hlf
  · left; exact bad_with_of_bad P _ _ _ hb
  rcases kinv_run P hC1 evs s hrun with hb | hK
  · left; exact bad_with_of_bad P _ _ _ hb
  rcases clean_or_bad P evs s ex with hb | ⟨hNC, -⟩
  · left; exact hb
  right
  intro hmem
  obtain ⟨tx, g, hm, hG, hkm, hsub⟩ := hK _ hmem
  set T := traceQueries P evs s ++ ex with hT
  obtain ⟨hi20, inr, val, hpos, h128, hc, hq⟩ := hlf o.e o.i hi
  have hQe : ∀ q ∈ eventQueries P (.spend tx g), q ∈ T := fun q hq' =>
    List.mem_append_left _ (Qe_in_trace P evs s q (by unfold Qe; exact List.mem_flatMap.2 ⟨_, hm, hq'⟩))
  have hwq : ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)), q ∈ T := fun q hq' =>
    hQe q (by simp only [eventQueries]; exact List.mem_append_left _ (List.mem_append_left _ hq'))
  have hdom : Query.dom P.c P.A (settleData tx).epoch ∈ T := hQe _ (by simp [eventQueries])
  obtain ⟨o3, o2, o1, od, -⟩ := opening_mem P o.e o.i sk ρ v
  rw [hleaf] at hkm
  obtain ⟨k, he, hidx, hlk, -⟩ := key_match P T hNC tx hG hwq hdom o.e o.i sk (cm (inner sk ρ) v) hi20
    (List.mem_append_right _ o3) (List.mem_append_right _ o2) (List.mem_append_right _ o1)
    (List.mem_append_right _ od) hkm
  have hvk := input_nonzero T hNC _ k _ hwq inr val hpos h128 (List.mem_append_left _ hq)
    (hc.symm.trans (hleaf.trans hlk))
  apply hns
  have ho : o = ⟨(settleData tx).epoch, (witOf (extOf P tx)).idx k⟩ := by
    cases o; simp only [Occ.mk.injEq]; exact ⟨he, hidx⟩
  rw [ho]; exact hsub _ (mem_inputsOf _ _ k hvk)


/-! ## Spendable -/

theorem spendable (P : Pool) (hC1 : C1) : Spendable P := by
  intro evs s hrun o sk ρ v hi hns hleaf n hin hn skd ρd f rcp auth hf hr0 hr ha0 ha hfresh
  dsimp only
  set xw := mkSpend P o.e ((s.leaves o.e).take n) o.i sk ρ v skd ρd f rcp auth with hxw
  set ex := openingQueries P o.e o.i sk ρ v ++ witnessQueries xw.1 xw.2 with hex
  rcases leaf_facts P hC1 evs s hrun with hb | hlf
  · left; exact bad_with_of_bad P _ _ _ hb
  rcases kinv_run P hC1 evs s hrun with hb | hK
  · left; exact bad_with_of_bad P _ _ _ hb
  rcases c5h P hC1 evs s hrun o sk ρ v hi hns hleaf with hb | hnf1
  · left; exact bad_with_sub P _ _ _ _ (fun q hq => List.mem_append_left _ hq) hb
  rcases clean_or_bad P evs s ex with hb | ⟨hNC, hND⟩
  · left; exact hb
  right
  set T := traceQueries P evs s ++ ex with hT
  obtain ⟨hi20, inr, val, hpos, h128, hc, hq⟩ := hlf o.e o.i hi
  have hqT : Query.h3 2 inr (val : F) ∈ T := List.mem_append_left _ hq
  obtain ⟨-, -, -, od, o4⟩ := opening_mem P o.e o.i sk ρ v
  have inO : ∀ q ∈ openingQueries P o.e o.i sk ρ v, q ∈ T := fun q h =>
    List.mem_append_right _ (List.mem_append_left _ h)
  have inW : ∀ q ∈ witnessQueries xw.1 xw.2, q ∈ T := fun q h =>
    List.mem_append_right _ (List.mem_append_right _ h)
  -- the opening's value is the leaf's
  have hv : v = (val : F) := ((h3_inj hNC hqT (inO _ o4) (hc.symm.trans hleaf)).2.2).symm
  have hvval : v.val = val := by
    rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans h128 (by norm_num [p]))]
  have hv0 : v ≠ 0 := by intro h; rw [h, ZMod.val_zero] at hf; omega
  obtain ⟨w2_0, w1_0, w3_0⟩ := mem_wq_nf xw.1 xw.2 0
  obtain ⟨w2_1, w1_1, w3_1⟩ := mem_wq_nf xw.1 xw.2 1
  obtain ⟨-, -, v3_0, -⟩ := mem_witnessQueries_k xw.1 xw.2 0
  obtain ⟨-, -, v3_1, -⟩ := mem_witnessQueries_k xw.1 xw.2 1
  -- R8's nullifier inequality
  have hnf : xw.1.nf1 ≠ xw.1.nf2 := by
    intro heq
    obtain ⟨-, hkey, hin'⟩ := h3_inj hNC (inW _ w3_0) (inW _ w3_1) heq
    obtain ⟨hl, -⟩ := h2_inj hNC (inW _ w1_0) (inW _ w1_1) hin'
    obtain ⟨-, -, hvv⟩ := h3_inj hNC (inW _ v3_0) (inW _ v3_1) hl
    apply hv0
    simpa [hxw, mkSpend] using hvv
  have hsink : SINK 0 ≠ SINK 1 := by
    intro h
    obtain ⟨q1, q2⟩ := sink_queries_in_trace P evs s
    have h' : H3 2 1 0 = H3 2 2 0 := by simpa [SINK, cm] using h
    obtain ⟨-, h12, -⟩ := h3_inj hNC (List.mem_append_left _ q1) (List.mem_append_left _ q2) h'
    exact one_ne_two_F h12
  have hR := mkSpend_R P o.e ((s.leaves o.e).take n) o.i sk ρ v skd ρd f rcp auth hi20
    (hvval ▸ h128) hf hr0 hr ha0 ha
    (spendable_R3 P o.e (s.leaves o.e) n o.i sk ρ v skd ρd f rcp auth hin hi20 hleaf) hnf hsink
  refine ⟨hR, fun h => hND _ (inW _ w3_0) h, fun h => hND _ (inW _ w3_1) h, ?_, ?_⟩
  · have : xw.1.nf1 = nf (D P.c P.A o.e) sk ((s.leaves o.e).getD o.i 0) o.i := by
      rw [hleaf]; simp [hxw, mkSpend, Witness.leaf]
    rw [this]; exact hnf1
  · intro hmem
    obtain ⟨tx, g, hm, hG, hkm, -⟩ := hK _ hmem
    have hQe : ∀ q ∈ eventQueries P (.spend tx g), q ∈ traceQueries P evs s := fun q hq' =>
      Qe_in_trace P evs s q (by unfold Qe; exact List.mem_flatMap.2 ⟨_, hm, hq'⟩)
    have hwq' : ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)),
        q ∈ traceQueries P evs s := fun q hq' =>
      hQe q (by simp only [eventQueries]; exact List.mem_append_left _ (List.mem_append_left _ hq'))
    have hdom : Query.dom P.c P.A (settleData tx).epoch ∈ T :=
      List.mem_append_left _ (hQe _ (by simp [eventQueries]))
    have hidx1 : xw.2.idx 1 < 2 ^ DEPTH := by simp [hxw, mkSpend]
    obtain ⟨k, he, -, -, hsk⟩ := key_match P T hNC tx hG (fun q h => List.mem_append_left _ (hwq' q h))
      hdom o.e (xw.2.idx 1) (xw.2.sk 1) (xw.2.leaf 1) hidx1
      (inW _ w3_1) (inW _ w2_1) (inW _ w1_1) (inO _ od) hkm
    apply hfresh
    obtain ⟨w2', -, -⟩ := mem_wq_nf (stmtOf (extOf P tx)) (witOf (extOf P tx)) k
    have := hwq' _ w2'
    rw [stmt_d P tx hG, ← he, ← hsk] at this
    exact this


theorem model_rest (hC1 : C1) (P : Pool) : C5g P ∧ C5h P ∧ Spendable P :=
  ⟨c5g P hC1, c5h P hC1, spendable P hC1⟩


end
end MSP
open MSP in
/-- The model half, given C5j and C5k, whose proofs are pending. -/
theorem model_theorem_of (h5j : ∀ P, C1 → C5j P) (h5k : ∀ P, C1 → C5k P) : ModelTheorem :=
  fun hC1 P =>
    ⟨c3 P hC1, c4 P hC1, c5a P hC1, c5b P hC1, c5c P hC1, c5d P, c5e P, c5g P hC1, c5h P hC1,
     c5i P hC1, h5j P hC1, h5k P hC1, spendable P hC1⟩
