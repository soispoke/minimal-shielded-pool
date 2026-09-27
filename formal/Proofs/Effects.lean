import Proofs.Model

/-! C5j to C5n and `StepFunctional` from C1, and `model_theorem`. -/

namespace MSP
noncomputable section
open Classical

/-! ## C5k -/

theorem tr_query_in_trace (P : Pool) (evs : List Event) (s : PoolState) (hcap : CapInv s) (e : ℕ) :
    Query.h2 (treeRoot 19 ((s.leaves e).take (2 ^ 19))) (treeRoot 19 ((s.leaves e).drop (2 ^ 19)))
      ∈ traceQueries P evs s := by
  apply tree_in_trace P evs s hcap e (s.leaves e).length le_rfl
  rw [List.take_length]
  show _ ∈ treeQueries 19 _ ++ treeQueries 19 _ ++ [_]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem c5k_exhibit (P : Pool) : ∀ evs s, Run P evs s → ∀ e ≤ s.E, e < 2 ^ 64 →
    BadEvent P evs s ∨
    Step P s (.publish e)
      { s with roots := s.roots ++ [(sourceId P.A e, s.slot, (TR (s.leaves e)).val)] } := by
  intro evs s hrun e he he64
  have finv := finInv_run P evs s hrun
  have hcap := capInv_run P evs s hrun
  by_cases h0 : TR (s.leaves e) = 0
  · left; right; left
    exact ⟨_, List.mem_append_left _ (tr_query_in_trace P evs s hcap e), h0⟩
  · right
    have hr : (if e = s.E then TR (s.leaves s.E) else s.finalRoot e) = TR (s.leaves e) := by
      split_ifs with hE
      · subst hE; rfl
      · exact finv e (lt_of_le_of_ne he hE)
    refine ⟨he64, he, ?_⟩
    show (if e = s.E then TR (s.leaves s.E) else s.finalRoot e) ≠ 0 ∧ _
    rw [hr]; exact ⟨h0, rfl⟩

/-! ## Exact accounting -/

theorem consume_one (s : PoolState) (e0 i0 : ℕ) (he : e0 ≤ s.E) (hi : i0 < (s.vals e0).length)
    (hn : (⟨e0, i0⟩ : Occ) ∉ s.spent) :
    occPart { s with spent := s.spent ++ [⟨e0, i0⟩] } + (s.vals e0).getD i0 0 = occPart s := by
  unfold occPart
  simp only
  have hin : ∀ e, ∑ i ∈ Finset.range (s.vals e).length, occG (s.spent ++ [⟨e0, i0⟩]) s.vals e i +
      (if e0 = e then (s.vals e0).getD i0 0 else 0) =
      ∑ i ∈ Finset.range (s.vals e).length, occG s.spent s.vals e i := by
    intro e
    by_cases hee : e0 = e
    · subst hee
      rw [if_pos rfl, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi),
        ← Finset.add_sum_erase (Finset.range _) (occG s.spent s.vals e0) (Finset.mem_range.2 hi)]
      have h1 : occG (s.spent ++ [⟨e0, i0⟩]) s.vals e0 i0 = 0 := by simp [occG]
      have h2 : occG s.spent s.vals e0 i0 = (s.vals e0).getD i0 0 := by simp [occG, hn]
      have h3 : ∑ i ∈ (Finset.range (s.vals e0).length).erase i0, occG (s.spent ++ [⟨e0, i0⟩]) s.vals e0 i =
          ∑ i ∈ (Finset.range (s.vals e0).length).erase i0, occG s.spent s.vals e0 i := by
        apply Finset.sum_congr rfl; intro i hi'
        have hne := Finset.ne_of_mem_erase hi'
        simp [occG, hne]
      rw [h1, h2, h3]; omega
    · rw [if_neg hee, add_zero]
      apply Finset.sum_congr rfl; intro i _
      have hee' : ¬ e = e0 := fun h => hee h.symm
      simp [occG, hee']
  rw [← Finset.sum_congr rfl (fun e _ => hin e), Finset.sum_add_distrib,
    Finset.sum_ite_eq (Finset.range (s.E + 1)), if_pos (Finset.mem_range.2 (by omega))]

theorem consume_eq (s : PoolState) (sd : SettleData) (w : Witness) (he : sd.epoch ≤ s.E)
    (hin : ∀ k, w.v k ≠ 0 → w.idx k < (s.vals sd.epoch).length ∧
      (s.vals sd.epoch).getD (w.idx k) 0 = (w.v k).val ∧ (⟨sd.epoch, w.idx k⟩ : Occ) ∉ s.spent)
    (hdist : w.v 0 ≠ 0 → w.v 1 ≠ 0 → w.idx 0 ≠ w.idx 1) :
    occPart { s with spent := s.spent ++ inputsOf sd w } + ((w.v 0).val + (w.v 1).val) = occPart s := by
  have hz : ∀ k, w.v k = 0 → (w.v k).val = 0 := by intro k hk; rw [hk, ZMod.val_zero]
  have hL : inputsOf sd w = (if w.v 0 ≠ 0 then [(⟨sd.epoch, w.idx 0⟩ : Occ)] else []) ++
      (if w.v 1 ≠ 0 then [(⟨sd.epoch, w.idx 1⟩ : Occ)] else []) := by
    unfold inputsOf; simp [List.finRange_succ]; split_ifs <;> simp_all
  have one := fun k hk => consume_one s sd.epoch (w.idx k) he (hin k hk).1 (hin k hk).2.2
  by_cases h0 : w.v 0 = 0 <;> by_cases h1 : w.v 1 = 0
  · rw [hL]; simp only [h0, h1, ne_eq, not_true_eq_false, if_false, List.append_nil, hz 0 h0, hz 1 h1]
    rfl
  · rw [hL]; simp only [h0, h1, ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true,
      List.nil_append, ZMod.val_zero, zero_add]
    have := one 1 h1; rw [(hin 1 h1).2.1] at this; exact this
  · rw [hL]; simp only [h0, h1, ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true,
      List.append_nil, ZMod.val_zero, add_zero]
    have := one 0 h0; rw [(hin 0 h0).2.1] at this; exact this
  · rw [hL]; simp only [h0, h1, ne_eq, not_false_eq_true, if_true, List.singleton_append]
    have hA := one 0 h0
    rw [(hin 0 h0).2.1] at hA
    have hB := consume_one { s with spent := s.spent ++ [⟨sd.epoch, w.idx 0⟩] } sd.epoch (w.idx 1) he
      (hin 1 h1).1 (by
        simp only [List.mem_append, List.mem_singleton, Occ.mk.injEq, true_and, not_or]
        exact ⟨(hin 1 h1).2.2, fun h => hdist h0 h1 h.symm⟩)
    simp only at hB
    rw [(hin 1 h1).2.1, show s.spent ++ [(⟨sd.epoch, w.idx 0⟩ : Occ)] ++ [⟨sd.epoch, w.idx 1⟩] =
      s.spent ++ [⟨sd.epoch, w.idx 0⟩, ⟨sd.epoch, w.idx 1⟩] by simp] at hB
    omega

theorem inner_update_eq (sp : List Occ) (vl : ℕ → List ℕ) (T : ℕ) (ns : List ℕ) (e : ℕ)
    (hf : ∀ o ∈ sp, o.i < (vl o.e).length) :
    ∑ i ∈ Finset.range ((Function.update vl T (vl T ++ ns)) e).length,
        occG sp (Function.update vl T (vl T ++ ns)) e i =
      ∑ i ∈ Finset.range (vl e).length, occG sp vl e i + (if e = T then ns.sum else 0) := by
  by_cases he : e = T
  · subst he
    simp only [Function.update_self, List.length_append, if_true]
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl; intro i hi
      simp only [occG, Function.update_self]
      rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hi)]
    · rw [← sum_getD ns]; apply Finset.sum_congr rfl; intro j _
      simp only [occG, Function.update_self]
      rw [if_neg]
      · rw [List.getD_append_right _ _ _ _ (by omega)]; simp
      · intro hm; have := hf _ hm; simp at this
  · simp only [Function.update_of_ne he, he, if_false, add_zero]
    apply Finset.sum_congr rfl; intro i _
    simp only [occG, Function.update_of_ne he]

theorem occPart_append_eq (s : PoolState) (new : List (F × ℕ)) (hv : ValsInv s)
    (hf : ∀ o ∈ s.spent, o.i < (s.vals o.e).length) :
    occPart (s.append new) = occPart s + (new.map Prod.snd).sum := by
  unfold PoolState.append occPart
  split_ifs with hr
  · simp only
    rw [Finset.sum_congr rfl fun e _ => inner_update_eq _ _ _ _ e hf]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (s.E + 1 + 1)), Finset.sum_range_succ,
      hv (s.E + 1) (by omega)]
    simp
  · simp only
    rw [Finset.sum_congr rfl fun e _ => inner_update_eq _ _ _ _ e hf]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (s.E + 1))]
    simp

theorem append_shape (s : PoolState) (new : List (F × ℕ)) :
    (s.append new).leaves (s.append new).E = s.leaves (s.append new).E ++ new.map Prod.fst ∧
    (s.append new).vals (s.append new).E = s.vals (s.append new).E ++ new.map Prod.snd ∧
    (s.append new).spent = s.spent ∧ (s.append new).credit = s.credit ∧ (s.append new).balance = s.balance := by
  unfold PoolState.append; split_ifs <;> simp

theorem append_paid (s : PoolState) (new : List (F × ℕ)) : (s.append new).paid = s.paid := by
  unfold PoolState.append; split_ifs <;> rfl

theorem mem_append_getD (L : List F) (Lv : List ℕ) (new : List (F × ℕ)) (hlen : Lv.length = L.length)
    (x : F × ℕ) (hx : x ∈ new) :
    ∃ i, L.length ≤ i ∧ i < (L ++ new.map Prod.fst).length ∧ (L ++ new.map Prod.fst).getD i 0 = x.1 ∧
      (Lv ++ new.map Prod.snd).getD i 0 = x.2 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  refine ⟨L.length + j, by omega, by simp; omega, ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hj]
  · rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hlen, hj]

/-- The strengthened C5j: the occurrences are new (index at or past the old length). -/
def C5jS (P : Pool) : Prop :=
  (∀ evs s inr v s', Run P evs s → Step P s (.shield inr v) s' →
    BadEvent P (evs ++ [.shield inr v]) s' ∨
    (s'.balance = s.balance + v ∧ owed s' = owed s + v ∧ ∃ i, (s.leaves s'.E).length ≤ i ∧ i < (s'.leaves s'.E).length ∧
      (s'.leaves s'.E).getD i 0 = cm inr (v : F) ∧ (s'.vals s'.E).getD i 0 = v ∧
      (⟨s'.E, i⟩ : Occ) ∉ s'.spent))
def C5jT (P : Pool) : Prop :=
  (∀ evs s tx g s', Run P evs s → Step P s (.spend tx g) s' → SettlePre s P (settleData tx) →
    BadEvent P (evs ++ [.spend tx g]) s' ∨
    let sd := settleData tx
    let w := witOf (extOf P tx)
    (s'.credit = s.credit + Finsupp.single sd.rcp sd.pub ∧ owed s' + sd.fee = owed s ∧
     ∀ k : Fin 2, w.ov k ≠ 0 → ∃ i, (s.leaves s'.E).length ≤ i ∧ i < (s'.leaves s'.E).length ∧
       (s'.leaves s'.E).getD i 0 = cm (w.oi k) (w.ov k) ∧
       (s'.vals s'.E).getD i 0 = (w.ov k).val ∧ (⟨s'.E, i⟩ : Occ) ∉ s'.spent))

theorem spent_lt (P : Pool) (evs : List Event) (s : PoolState) (hinv : BInv P evs s) :
    ∀ o ∈ s.spent, o.i < (s.vals o.e).length := by
  intro o ho
  have := (hinv.2 o ho).1
  rw [← (hinv.1 o.e).length_eq]; exact this

theorem c5j_shield (P : Pool) (hC1 : C1) : C5jS P := by
  intro evs s inr v s' hrun hs
  have hg := grows_step P s s' _ hs
  rcases binv_run P hC1 evs s hrun with hb | hinv
  · left; exact bad_mono P (List.prefix_append _ _) hg [] hb
  right
  have hvi := valsInv_run P evs s hrun
  have hf := spent_lt P evs s hinv
  obtain ⟨h0, h128, -, -, -, rfl⟩ := hs
  obtain ⟨hl, hv, hsp, hc, hb⟩ := append_shape s [(cm inr v, v)]
  refine ⟨by simp, ?_, ?_⟩
  · rw [owed_eq, owed_eq]
    change occPart (s.append _) + credSum (s.append _).credit = _
    rw [occPart_append_eq s _ hvi hf, hc]; simp; omega
  · obtain ⟨i, hi1, hi2, hi3, hi4⟩ := mem_append_getD (s.leaves (s.append [(cm inr v, v)]).E)
      (s.vals (s.append [(cm inr v, v)]).E) [(cm inr v, v)] ((hinv.1 _).length_eq.symm) _ (List.mem_singleton_self _)
    refine ⟨i, hi1, ?_, ?_, ?_, ?_⟩
    · show i < ((s.append _).leaves (s.append _).E).length; rw [hl]; exact hi2
    · show ((s.append _).leaves (s.append _).E).getD i 0 = _; rw [hl]; exact hi3
    · show ((s.append _).vals (s.append _).E).getD i 0 = _; rw [hv]; exact hi4
    · show _ ∉ (s.append _).spent
      rw [hsp]; intro hm; have := hf _ hm
      rw [(hinv.1 _).length_eq.symm] at this
      simp at this; omega

theorem c5j_settle (P : Pool) (hC1 : C1) : C5jT P := by
  intro evs s tx g s' hrun hs hpre
  have hg := grows_step P s s' _ hs
  rcases binv_run P hC1 evs s hrun with hb | hinv
  · left; exact bad_mono P (List.prefix_append _ _) hg [] hb
  rcases good_spend P hC1 evs s tx g s' hrun hs with hb | hG
  · left; exact hb
  rcases c5b P hC1 evs s tx g s' hrun hs with hb | ⟨hin, hdist⟩
  · left; exact hb
  set sd := settleData tx with hsd
  set w := witOf (extOf P tx) with hw
  have hq := sink_queries_in_trace P (evs ++ [.spend tx g]) s'
  have hoq : Query.h3 2 (w.oi 0) (w.ov 0) ∈ traceQueries P (evs ++ [.spend tx g]) s' ∧
      Query.h3 2 (w.oi 1) (w.ov 1) ∈ traceQueries P (evs ++ [.spend tx g]) s' := by
    constructor <;> simp [traceQueries, eventQueries, witnessQueries, w]
  by_cases hc0 : (Query.h3 2 (w.oi 0) (w.ov 0)).collide (Query.h3 2 1 0)
  · left; left; exact ⟨_, List.mem_append_left _ hoq.1, _, List.mem_append_left _ hq.1, hc0⟩
  by_cases hc1 : (Query.h3 2 (w.oi 1) (w.ov 1)).collide (Query.h3 2 2 0)
  · left; left; exact ⟨_, List.mem_append_left _ hoq.2, _, List.mem_append_left _ hq.2, hc1⟩
  right
  obtain ⟨hp128, hf128⟩ : sd.pub < 2 ^ 128 ∧ sd.fee < 2 ^ 128 := ⟨hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have heE : sd.epoch ≤ s.E := hpre.2.2.2.2.2.2.2.1
  have hR := hG.R
  obtain ⟨-, -, -, -, ho1, ho2, -, hsum, -, -, -⟩ := hR
  simp only [stmtOfTx, SettleData.stmt] at hsum ho1 ho2
  simp only [← hsd, ← hw] at hsum ho1 ho2
  simp only [val_cast_lt hp128, val_cast_lt hf128] at hsum
  have hs0 : sd.o1 = (SINK 0).val → w.ov 0 = 0 := by
    intro h
    have hcm : H3 2 (w.oi 0) (w.ov 0) = H3 2 1 0 := by
      have : cm (w.oi 0) (w.ov 0) = SINK 0 := by rw [← ho1, h, ZMod.natCast_zmod_val]
      simpa [SINK, cm] using this
    by_contra hne
    exact hc0 ⟨by simp [hne], hcm⟩
  have hs1 : sd.o2 = (SINK 1).val → w.ov 1 = 0 := by
    intro h
    have hcm : H3 2 (w.oi 1) (w.ov 1) = H3 2 2 0 := by
      have : cm (w.oi 1) (w.ov 1) = SINK 1 := by rw [← ho2, h, ZMod.natCast_zmod_val]
      simpa [SINK, cm, one_add_one_eq_two] using this
    by_contra hne
    exact hc1 ⟨by simp [hne], hcm⟩
  have hnew : ((newLeaves sd w).map Prod.snd).sum = (w.ov 0).val + (w.ov 1).val := by
    unfold newLeaves; split_ifs with h1 h2 h2 <;> simp [hs0, hs1, h1, h2]
  have hmem : ∀ k : Fin 2, w.ov k ≠ 0 → (cm (w.oi k) (w.ov k), (w.ov k).val) ∈ newLeaves sd w := by
    intro k hk
    fin_cases k
    · have : sd.o1 ≠ (SINK 0).val := fun h => hk (hs0 h)
      simp [newLeaves, this, ← ho1]
    · have : sd.o2 ≠ (SINK 1).val := fun h => hk (hs1 h)
      simp [newLeaves, this, ← ho2]
  obtain ⟨-, -, -, -, -, -, -, hs'⟩ := hs
  set s1 : PoolState := ({ s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf sd w, balance := s.balance - g } : PoolState) with hs1def
  set s2 := s1.append (newLeaves sd w) with hs2def
  have hf1 : ∀ o ∈ s1.spent, o.i < (s1.vals o.e).length := by
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact spent_lt P evs s hinv o ho
    · unfold inputsOf at ho
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ho
      obtain ⟨k, hk, rfl⟩ := ho
      show w.idx k < (s.vals sd.epoch).length
      rw [← (hinv.1 _).length_eq]; exact (hin k hk).1
  have hin' : ∀ k, w.v k ≠ 0 → w.idx k < (s.vals sd.epoch).length ∧
      (s.vals sd.epoch).getD (w.idx k) 0 = (w.v k).val ∧ (⟨sd.epoch, w.idx k⟩ : Occ) ∉ s.spent := by
    intro k hk
    obtain ⟨h1, -, h3, h4⟩ := hin k hk
    exact ⟨by rw [← (hinv.1 _).length_eq]; exact h1, h3, h4⟩
  have hocc1 : occPart s1 + ((w.v 0).val + (w.v 1).val) = occPart s := consume_eq s sd w heE hin' hdist
  have hocc2 : occPart s2 = occPart s1 + ((newLeaves sd w).map Prod.snd).sum :=
    occPart_append_eq s1 _ (valsInv_run P evs s hrun) hf1
  obtain ⟨hl, hv, hsp, hc, -⟩ := append_shape s1 (newLeaves sd w)
  have key : s'.E = s2.E ∧ s'.leaves = s2.leaves ∧ s'.vals = s2.vals ∧ s'.spent = s2.spent ∧
      s'.credit = s2.credit + Finsupp.single sd.rcp sd.pub := by
    dsimp only at hs'
    subst hs'
    by_cases h1 : SettlePre s P (settleData tx)
    · rw [if_pos h1]
      by_cases hp : (settleData tx).pub = 0
      · rw [if_pos hp]
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        show s2.credit = s2.credit + Finsupp.single sd.rcp sd.pub
        rw [show sd.pub = 0 from hp]; simp
      · rw [if_neg hp]
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd hpre h1
  obtain ⟨kE, kl, kv, ksp, kc⟩ := key
  have hocc' : occPart s' = occPart s2 := by unfold occPart; rw [kE, kv, ksp]
  refine ⟨by rw [kc, hc], ?_, ?_⟩
  · rw [owed_eq, owed_eq, hocc', kc, credSum_add_single, hc]
    change occPart s2 + (credSum s.credit + sd.pub) + sd.fee = occPart s + credSum s.credit
    omega
  · intro k hk
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := mem_append_getD (s1.leaves s2.E) (s1.vals s2.E) (newLeaves sd w)
      ((hinv.1 _).length_eq.symm) _ (hmem k hk)
    refine ⟨i, by rw [kE]; exact hi1, ?_, ?_, ?_, ?_⟩
    · rw [kE, kl, hl]; exact hi2
    · rw [kE, kl, hl]; exact hi3
    · rw [kE, kv, hv]; exact hi4
    · rw [kE, ksp, hsp]; intro hm; have := hf1 _ hm
      change i < (s.vals s2.E).length at this
      rw [(hinv.1 _).length_eq.symm] at this
      change (s.leaves s2.E).length ≤ i at hi1
      omega

theorem c5j (P : Pool) (hC1 : C1) : C5j P := by
  refine ⟨fun evs s inr v s' hr hs => ?_, fun evs s tx g s' hr hs hp => ?_⟩
  · rcases c5j_shield P hC1 evs s inr v s' hr hs with hb | ⟨-, -, h⟩
    · exact Or.inl hb
    · exact Or.inr h
  · rcases c5j_settle P hC1 evs s tx g s' hr hs hp with hb | ⟨-, -, h3⟩
    · exact Or.inl hb
    · right; intro _ k hk
      exact h3 k hk

theorem step_functional (P : Pool) : StepFunctional P := by
  intro s e s₁ s₂ h1 h2
  cases e with
  | shield inr v => rw [h1.2.2.2.2.2, h2.2.2.2.2.2]
  | publish e => rw [h1.2.2.2, h2.2.2.2]
  | rootWrite a salt r => rw [h1.2.2, h2.2.2]
  | claim r => rw [h1.2.2, h2.2.2]
  | receive v => rw [h1, h2]
  | tick => rw [h1, h2]
  | spend tx g => rw [h1.2.2.2.2.2.2.2, h2.2.2.2.2.2.2.2]

theorem c5l (P : Pool) (hC1 : C1) : C5l P := by
  intro evs s ev s' hrun hs
  have hg := grows_step P s s' ev hs
  cases ev with
  | shield inr v =>
    rcases c5j_shield P hC1 evs s inr v s' hrun hs with hb | ⟨h1, h2, -⟩
    · exact Or.inl hb
    · right
      obtain ⟨-, -, -, -, -, rfl⟩ := hs
      obtain ⟨-, -, -, hc, -⟩ := append_shape s [(cm inr v, v)]
      exact ⟨h1, hc, by unfold PoolState.append; split_ifs <;> rfl, h2⟩
  | publish e => obtain ⟨-, -, -, rfl⟩ := hs; right; exact ⟨rfl, rfl, rfl, rfl⟩
  | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; right; exact ⟨rfl, rfl, rfl, rfl⟩
  | tick => subst hs; right; exact ⟨rfl, rfl, rfl, rfl⟩
  | receive v => subst hs; right; exact ⟨rfl, rfl, rfl, rfl⟩
  | claim r =>
    obtain ⟨-, hle, rfl⟩ := hs
    right
    refine ⟨by simp only; omega, rfl, rfl, ?_⟩
    rw [owed_eq, owed_eq]
    change occPart s + credSum (s.credit.erase r) + s.credit r = occPart s + credSum s.credit
    have := credSum_erase s.credit r
    omega
  | spend tx g =>
    have hbal : s'.balance + g = s.balance ∧ s'.paid = s.paid := by
      obtain ⟨-, -, -, -, -, hmc, hgas, hs'⟩ := hs
      subst hs'
      split_ifs with h1 h2
      · refine ⟨?_, by rw [append_paid]⟩
        rw [(credit_append _ _).2.1]; simp only; omega
      · refine ⟨?_, by show (PoolState.append _ _).paid = _; rw [append_paid]⟩
        show (PoolState.append _ _).balance + g = s.balance
        rw [(credit_append _ _).2.1]; simp only; omega
      · exact ⟨by simp only; omega, rfl⟩
    by_cases hpre : SettlePre s P (settleData tx)
    · rcases c5j_settle P hC1 evs s tx g s' hrun hs hpre with hb | ⟨h1, h2, -⟩
      · exact Or.inl hb
      · right; exact ⟨hbal.1, hbal.2, fun _ => ⟨h1, h2⟩, fun h => absurd hpre h⟩
    · right
      refine ⟨hbal.1, hbal.2, fun h => absurd h hpre, fun _ => ?_⟩
      obtain ⟨-, -, -, -, -, -, -, hs'⟩ := hs
      dsimp only at hs'
      rw [if_neg hpre] at hs'
      subst hs'
      refine ⟨rfl, ?_⟩
      rw [owed_eq, owed_eq]
      apply Nat.add_le_add_right
      unfold occPart
      apply Finset.sum_le_sum; intro e _
      apply Finset.sum_le_sum; intro i _
      exact occG_mono _ _ _ _ _

end
end MSP

namespace MSP

noncomputable section
open Classical

theorem c5m (P : Pool) : C5m P := by
  intro s e s' hs
  cases e with
  | shield inr v => obtain ⟨-, -, -, -, -, rfl⟩ := hs; show (s.append _).roots = _; unfold PoolState.append; split_ifs <;> rfl
  | publish e => trivial
  | rootWrite a salt r => obtain ⟨-, -, rfl⟩ := hs; exact ⟨_, rfl⟩
  | claim r => obtain ⟨-, -, rfl⟩ := hs; rfl
  | receive v => subst hs; rfl
  | tick => subst hs; rfl
  | spend tx g =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
    dsimp only
    split_ifs <;> first | rfl | (unfold PoolState.append; split_ifs <;> rfl)

theorem c5k (P : Pool) : C5k P := ⟨fun _ _ _ h => ⟨h.2.1, h.1⟩, c5k_exhibit P⟩

theorem append_E (s : PoolState) (new : List (F × ℕ)) :
    (s.append new).E = if rollsOver s new.length then s.E + 1 else s.E := by
  unfold PoolState.append; split_ifs <;> rfl

theorem newLeaves_length (sd : SettleData) (w : Witness) : (newLeaves sd w).length = newCount sd := by
  unfold newLeaves newCount; split_ifs <;> simp

theorem c5n (P : Pool) : C5n P := by
  intro s e s' h
  cases e with
  | shield inr v =>
    obtain ⟨-, -, -, -, -, rfl⟩ := h
    show (s.append _).E = s.E ∨ ((s.append _).E = s.E + 1 ∧ rollsOver s 1)
    rw [append_E]; simp only [List.length_singleton]
    split_ifs with hr
    · exact Or.inr ⟨rfl, hr⟩
    · exact Or.inl rfl
  | publish e => obtain ⟨-, -, -, rfl⟩ := h; exact Or.inl rfl
  | rootWrite a salt r => obtain ⟨-, -, rfl⟩ := h; exact Or.inl rfl
  | claim r => obtain ⟨-, -, rfl⟩ := h; exact Or.inl rfl
  | receive v => subst h; exact Or.inl rfl
  | tick => subst h; exact Or.inl rfl
  | spend tx g =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := h
    by_cases hp : SettlePre s P (settleData tx)
    · have key : ∀ t : PoolState, t.E = (PoolState.append
          { s with keys := s.keys ++ tx.nonceKeys,
                   spent := s.spent ++ inputsOf (settleData tx) (witOf (extOf P tx)),
                   balance := s.balance - g } (newLeaves (settleData tx) (witOf (extOf P tx)))).E →
          t.E = s.E ∨ (t.E = s.E + 1 ∧ SettlePre s P (settleData tx) ∧
            rollsOver s (newCount (settleData tx))) := by
        intro t ht
        rw [ht, append_E, newLeaves_length]
        split_ifs with hr
        · exact Or.inr ⟨rfl, hp, hr⟩
        · exact Or.inl rfl
      simp only [if_pos hp]
      split_ifs with h0
      · exact key _ rfl
      · exact key _ rfl
    · simp only [if_neg hp]; first | exact Or.inl rfl | exact Or.inl trivial | simp

theorem model_theorem : ModelTheorem :=
  model_theorem_of (fun P h => c5j P h) (fun P _ => c5k P) (fun P h => c5l P h) c5m c5n
    step_functional

end

end MSP
