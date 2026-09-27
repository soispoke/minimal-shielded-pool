import Proofs.C5i

/-! C5b from C1, through an invariant: every leaf's creation query is in the
trace, and every spent occurrence's nullifier, under the opening that spent it,
is a consumed key. -/

namespace MSP
noncomputable section
open Classical

def Qe (P : Pool) (evs : List Event) : List Query := evs.flatMap (eventQueries P)

theorem Qe_mono (P : Pool) (evs t : List Event) : ∀ q ∈ Qe P evs, q ∈ Qe P (evs ++ t) := by
  intro q hq; unfold Qe at *; rw [List.flatMap_append]; exact List.mem_append_left _ hq

theorem Qe_in_trace (P : Pool) (evs : List Event) (s : PoolState) :
    ∀ q ∈ Qe P evs, q ∈ traceQueries P evs s := by
  intro q hq
  unfold traceQueries
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ hq

theorem wq_in_Qe (P : Pool) (evs : List Event) (tx : FrameTx) (g : ℕ) :
    ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)), q ∈ Qe P (evs ++ [.spend tx g]) := by
  intro q hq; unfold Qe; rw [List.mem_flatMap]
  exact ⟨.spend tx g, by simp, by
    simp only [eventQueries]; exact List.mem_append_left _ (List.mem_append_left _ hq)⟩

def LeafOK (P : Pool) (evs : List Event) (c : F) (v : ℕ) : Prop :=
  v < 2 ^ 128 ∧ ∃ inr, c = cm inr (v : F) ∧ Query.h3 2 inr (v : F) ∈ Qe P evs

def SpentOK (P : Pool) (evs : List Event) (s : PoolState) (o : Occ) : Prop :=
  o.i < (s.leaves o.e).length ∧ ∃ sk ρ v : F,
    (s.leaves o.e).getD o.i 0 = cm (inner sk ρ) v ∧
    Query.h3 1 sk 0 ∈ Qe P evs ∧ Query.h2 (pk sk) ρ ∈ Qe P evs ∧
    Query.h3 2 (inner sk ρ) v ∈ Qe P evs ∧
    (nf (D P.c P.A o.e) sk ((s.leaves o.e).getD o.i 0) o.i).val ∈ s.keys

def BInv (P : Pool) (evs : List Event) (s : PoolState) : Prop :=
  (∀ e, List.Forall₂ (LeafOK P evs) (s.leaves e) (s.vals e)) ∧ (∀ o ∈ s.spent, SpentOK P evs s o)

theorem leafOK_mono (P : Pool) (evs t : List Event) (c : F) (v : ℕ) :
    LeafOK P evs c v → LeafOK P (evs ++ t) c v := by
  rintro ⟨h1, inr, h2, h3⟩; exact ⟨h1, inr, h2, Qe_mono P evs t _ h3⟩

theorem getD_prefix {L L' : List F} (h : L <+: L') {i : ℕ} (hi : i < L.length) :
    L'.getD i 0 = L.getD i 0 := by
  obtain ⟨t, rfl⟩ := h; exact List.getD_append _ _ _ _ hi

theorem spentOK_mono (P : Pool) (evs evs' : List Event) (s s' : PoolState) (o : Occ)
    (hq : ∀ q ∈ Qe P evs, q ∈ Qe P evs')
    (hl : ∀ e, s.leaves e <+: s'.leaves e) (hk : ∀ x ∈ s.keys, x ∈ s'.keys) :
    SpentOK P evs s o → SpentOK P evs' s' o := by
  rintro ⟨hi, sk, ρ, v, hc, q1, q2, q3, hkey⟩
  have hg := getD_prefix (hl o.e) hi
  refine ⟨lt_of_lt_of_le hi (hl o.e).length_le, sk, ρ, v, by rw [hg, hc], hq _ q1,
    hq _ q2, hq _ q3, by rw [hg]; exact hk _ hkey⟩

theorem f2_append (Rl : F → ℕ → Prop) (s : PoolState) (new : List (F × ℕ))
    (hs : ∀ e, List.Forall₂ Rl (s.leaves e) (s.vals e)) (h : ∀ x ∈ new, Rl x.1 x.2) :
    ∀ e, List.Forall₂ Rl ((s.append new).leaves e) ((s.append new).vals e) := by
  have hn : List.Forall₂ Rl (new.map Prod.fst) (new.map Prod.snd) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]; exact h
  intro e
  unfold PoolState.append
  split_ifs <;>
  · simp only [Function.update_apply]
    split_ifs
    · exact List.rel_append (hs _) hn
    · exact hs e

theorem append_keys_spent (s : PoolState) (new : List (F × ℕ)) :
    (s.append new).keys = s.keys ∧ (s.append new).spent = s.spent := by
  unfold PoolState.append; split_ifs <;> exact ⟨rfl, rfl⟩

theorem forall₂_getD {Rl : F → ℕ → Prop} {l1 : List F} {l2 : List ℕ} (h : List.Forall₂ Rl l1 l2)
    {i : ℕ} (hi : i < l1.length) : Rl (l1.getD i 0) (l2.getD i 0) := by
  have hl := h.length_eq
  have hi' : i < l2.length := hl ▸ hi
  rw [List.forall₂_iff_get] at h
  have := h.2 i hi hi'
  simp only [List.get_eq_getElem] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
    Option.getD_some]
  exact this

theorem tree_in_trace (P : Pool) (evs : List Event) (s : PoolState) (hcap : CapInv s) (e n : ℕ)
    (hn : n ≤ (s.leaves e).length) :
    ∀ q ∈ treeQueries DEPTH ((s.leaves e).take n), q ∈ traceQueries P evs s := by
  intro q hq
  by_cases he : e ≤ s.E
  · unfold traceQueries; apply List.mem_append_right; rw [List.mem_flatMap]
    refine ⟨e, List.mem_range.2 (by omega), ?_⟩
    apply List.mem_append_right; rw [List.mem_flatMap]
    exact ⟨n, List.mem_range.2 (by omega), hq⟩
  · have hl : s.leaves e = [] := hcap.2 e (by omega)
    rw [hl] at hq
    unfold traceQueries; apply List.mem_append_right; rw [List.mem_flatMap]
    refine ⟨0, List.mem_range.2 (by omega), ?_⟩
    apply List.mem_append_right; rw [List.mem_flatMap]
    exact ⟨0, List.mem_range.2 (by omega), by simpa using hq⟩

theorem out_mem (x : Statement) (w : Witness) :
    Query.h3 2 (w.oi 0) (w.ov 0) ∈ witnessQueries x w ∧ Query.h3 2 (w.oi 1) (w.ov 1) ∈ witnessQueries x w := by
  constructor <;> simp [witnessQueries]

/-- The nullifier of each input, under its extracted opening, is one of the consumed keys. -/
theorem nf_key (P : Pool) (tx : FrameTx) (hacc : Acc P.A P.c P.verifies 1 tx)
    (hR : R (stmtOfTx tx) (witOf (extOf P tx)))
    (hkeys : tx.nonceKeys = [min (settleData tx).nf1 (settleData tx).nf2,
                             max (settleData tx).nf1 (settleData tx).nf2]) :
    ∀ k, (nf (D P.c P.A (settleData tx).epoch) ((witOf (extOf P tx)).sk k)
      ((witOf (extOf P tx)).leaf k) ((witOf (extOf P tx)).idx k)).val ∈ tx.nonceKeys := by
  obtain ⟨f0, f1, f2, rest, hfr, -, -, -, -, -, hA5, -, -⟩ := hacc
  have hsd : settleData tx = SettleData.decode f2.data := by simp [settleData, hfr]
  rw [← hsd] at hA5
  obtain ⟨-, -, -, -, hn1, hn2, -, -, -, -, -, -, -, -, hdom⟩ := hA5
  obtain ⟨-, h2a, h2b, -⟩ := hR
  have hd : ((settleData tx).domain : F) = D P.c P.A (settleData tx).epoch := by
    rw [hdom, ZMod.natCast_zmod_val]
  simp only [stmtOfTx, SettleData.stmt] at h2a h2b
  rw [hd] at h2a h2b
  intro k
  fin_cases k
  · show (nf (D P.c P.A (settleData tx).epoch) ((witOf (extOf P tx)).sk 0)
      ((witOf (extOf P tx)).leaf 0) ((witOf (extOf P tx)).idx 0)).val ∈ tx.nonceKeys
    rw [← h2a, ZMod.val_natCast, Nat.mod_eq_of_lt hn1, hkeys]
    rcases le_total (settleData tx).nf1 (settleData tx).nf2 with h | h
    · simp [min_eq_left h]
    · simp [max_eq_left h]
  · show (nf (D P.c P.A (settleData tx).epoch) ((witOf (extOf P tx)).sk 1)
      ((witOf (extOf P tx)).leaf 1) ((witOf (extOf P tx)).idx 1)).val ∈ tx.nonceKeys
    rw [← h2b, ZMod.val_natCast, Nat.mod_eq_of_lt hn2, hkeys]
    rcases le_total (settleData tx).nf1 (settleData tx).nf2 with h | h
    · simp [max_eq_right h]
    · simp [min_eq_right h]

/-- The C5b conclusion at one spend step, from the invariant and C3's conclusion,
when the step's trace has no collision and no degenerate output. -/
theorem core (P : Pool) (evs : List Event) (s s' : PoolState) (tx : FrameTx) (g : ℕ)
    (hrun : Run P evs s) (hinv : BInv P evs s) (hs : Step P s (.spend tx g) s')
    (hNC : NoColl (traceQueries P (evs ++ [.spend tx g]) s'))
    (hND : ∀ q ∈ traceQueries P (evs ++ [.spend tx g]) s', ¬ q.degenerate)
    (hR : R (stmtOfTx tx) (witOf (extOf P tx)))
    (hkeys : tx.nonceKeys = [min (settleData tx).nf1 (settleData tx).nf2,
                             max (settleData tx).nf1 (settleData tx).nf2])
    (hroot : ∃ n ≤ (s.leaves (settleData tx).epoch).length,
        ((settleData tx).root : F) = TR ((s.leaves (settleData tx).epoch).take n)) :
    let w := witOf (extOf P tx)
    let e := (settleData tx).epoch
    (∀ k, w.v k ≠ 0 →
      w.idx k < (s.leaves e).length ∧ (s.leaves e).getD (w.idx k) 0 = w.leaf k ∧
      (s.vals e).getD (w.idx k) 0 = (w.v k).val ∧ (⟨e, w.idx k⟩ : Occ) ∉ s.spent) ∧
    (w.v 0 ≠ 0 → w.v 1 ≠ 0 → w.idx 0 ≠ w.idx 1) := by
  intro w e
  have hg := grows_step P s s' _ hs
  have hcap' := capInv_run P _ s' (Run.snoc hrun hs)
  obtain ⟨n, hn, hrt⟩ := hroot
  have hnk := nf_key P tx hs.1 hR hkeys
  have hfresh : ∀ k ∈ tx.nonceKeys, k ∉ s.keys := hs.2.2.2.1
  set T := traceQueries P (evs ++ [.spend tx g]) s'
  set L := s.leaves e
  have inT : ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) w, q ∈ T := spend_wq_in_trace P evs tx g s'
  have QeT : ∀ q ∈ Qe P evs, q ∈ T := fun q hq =>
    Qe_in_trace P (evs ++ [.spend tx g]) s' q (Qe_mono P evs _ q hq)
  have hR' := hR
  obtain ⟨hR1, hR2a, hR2b, hR3, -, -, -, -, -, -, hR8a, -⟩ := hR'
  have treeT : ∀ q ∈ treeQueries DEPTH (L.take n), q ∈ T := by
    intro q hq
    rw [← take_of_prefix (hg.leaves e) hn] at hq
    exact tree_in_trace P _ s' hcap' e n (hn.trans (hg.leaves e).length_le) q hq
  have leafEq : ∀ k, w.v k ≠ 0 → w.idx k < L.length ∧ L.getD (w.idx k) 0 = w.leaf k := by
    intro k hk
    have hmr : MR (w.leaf k) (w.idx k) (w.sib k) = TR (L.take n) := by
      rw [hR3 k hk]; exact hrt
    have hw := path_walk T hNC (w.leaf k) (w.idx k) (w.sib k) (L.take n) (hR1 k)
      (fun q hq => inT q ((mem_witnessQueries_k _ w k).2.2.2 q hq)) treeT hmr
    by_cases hlt : w.idx k < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt, ← List.getD_eq_getElem?_getD] at hw
      exact ⟨lt_of_lt_of_le hlt hn, hw.symm⟩
    · exfalso
      rw [List.getD_eq_default _ _ (by simp; omega)] at hw
      exact hND _ (inT _ (mem_witnessQueries_k _ w k).2.2.1) hw
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨hlt, hL⟩ := leafEq k hk
    obtain ⟨w1, w2, w3, -⟩ := mem_witnessQueries_k (stmtOf (extOf P tx)) w k
    refine ⟨hlt, hL, ?_, ?_⟩
    · -- the value, from the leaf's creation query
      obtain ⟨hv128, inr, hc, hq⟩ := forall₂_getD (hinv.1 e) hlt
      have heq : H3 2 inr (((s.vals e).getD (w.idx k) 0 : ℕ) : F) = H3 2 (inner (w.sk k) (w.ρ k)) (w.v k) := by
        have := hc.symm.trans hL; exact this
      have := (h3_inj hNC (QeT _ hq) (inT _ w3) heq).2.2
      rw [← this, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hv128 (by norm_num [p]))]
    · -- not consumed before, by key freshness
      intro hmem
      obtain ⟨-, sk', ρ', v', hc, q1, q2, q3, hkey⟩ := hinv.2 _ hmem
      have heq : H3 2 (inner (w.sk k) (w.ρ k)) (w.v k) = H3 2 (inner sk' ρ') v' := by
        have := hL.symm.trans hc; exact this
      obtain ⟨-, hin, -⟩ := h3_inj hNC (inT _ w3) (QeT _ q3) heq
      obtain ⟨hpk, -⟩ := h2_inj hNC (inT _ w2) (QeT _ q2) hin
      obtain ⟨-, hsk, -⟩ := h3_inj hNC (inT _ w1) (QeT _ q1) hpk
      change (nf (D P.c P.A e) sk' (L.getD (w.idx k) 0) (w.idx k)).val ∈ s.keys at hkey
      rw [hL, ← hsk] at hkey
      exact hfresh _ (hnk k) hkey
  · intro h0 h1 hidx
    obtain ⟨-, hL0⟩ := leafEq 0 h0
    obtain ⟨-, hL1⟩ := leafEq 1 h1
    rw [hidx] at hL0
    have hleq : w.leaf 0 = w.leaf 1 := hL0.symm.trans hL1
    obtain ⟨w01, w02, w03, -⟩ := mem_witnessQueries_k (stmtOf (extOf P tx)) w 0
    obtain ⟨w11, w12, w13, -⟩ := mem_witnessQueries_k (stmtOf (extOf P tx)) w 1
    obtain ⟨-, hin, -⟩ := h3_inj hNC (inT _ w03) (inT _ w13) hleq
    obtain ⟨hpk, -⟩ := h2_inj hNC (inT _ w02) (inT _ w12) hin
    obtain ⟨-, hsk, -⟩ := h3_inj hNC (inT _ w01) (inT _ w11) hpk
    apply hR8a
    rw [hR2a, hR2b, hsk, hleq, hidx]


theorem binv_run (P : Pool) (hC1 : C1) : ∀ evs s, Run P evs s → BadEvent P evs s ∨ BInv P evs s := by
  intro evs s h
  induction h with
  | nil => right; exact ⟨fun e => by simp [PoolState.init], fun o ho => by simp [PoolState.init] at ho⟩
  | @snoc evs s ev s' hrun hs ih =>
    have hg := grows_step P s s' ev hs
    rcases ih with hb | hinv
    · left; exact bad_mono P (List.prefix_append _ _) hg [] hb
    have base1 : ∀ e, List.Forall₂ (LeafOK P (evs ++ [ev])) (s.leaves e) (s.vals e) :=
      fun e => (hinv.1 e).imp (fun {c v} => leafOK_mono P evs [ev] c v)
    have same : ∀ s'' : PoolState, s''.leaves = s.leaves → s''.vals = s.vals → s''.spent = s.spent →
        s''.keys = s.keys → BInv P (evs ++ [ev]) s'' := by
      intro s'' h1 h2 h3 h4
      refine ⟨fun e => by rw [h1, h2]; exact base1 e, fun o ho => ?_⟩
      rw [h3] at ho
      exact spentOK_mono P evs _ s s'' o (Qe_mono P evs [ev]) (fun e => by rw [h1])
        (fun x hx => by rw [h4]; exact hx) (hinv.2 o ho)
    cases ev with
    | shield inr v =>
      obtain ⟨h0, h128, -, -, -, rfl⟩ := hs
      right
      obtain ⟨hk, hsp⟩ := append_keys_spent s [(cm inr v, v)]
      refine ⟨f2_append _ s _ base1 ?_, fun o ho => ?_⟩
      · intro x hx; simp at hx; subst hx
        exact ⟨h128, inr, rfl, by
          unfold Qe; rw [List.mem_flatMap]; exact ⟨.shield inr v, by simp, by simp [eventQueries]⟩⟩
      · have ho' : o ∈ s.spent := by rw [← hsp]; exact ho
        exact spentOK_mono P evs _ s _ o (Qe_mono P evs _) hg.leaves
          (fun x hx => by show x ∈ (s.append _).keys; rw [hk]; exact hx) (hinv.2 o ho')
    | publish e => obtain ⟨-, -, -, rfl⟩ := hs; right; exact same _ rfl rfl rfl rfl
    | rootWrite a salt x => obtain ⟨-, -, rfl⟩ := hs; right; exact same _ rfl rfl rfl rfl
    | claim r => obtain ⟨-, -, rfl⟩ := hs; right; exact same _ rfl rfl rfl rfl
    | receive v => subst hs; right; exact same _ rfl rfl rfl rfl
    | tick => subst hs; right; exact same _ rfl rfl rfl rfl
    | spend tx g =>
      by_cases hNC : NoColl (traceQueries P (evs ++ [.spend tx g]) s')
      swap
      · left; left; unfold NoColl at hNC; push Not at hNC
        obtain ⟨q1, h1, q2, h2, hc⟩ := hNC
        exact ⟨q1, List.mem_append_left _ h1, q2, List.mem_append_left _ h2, hc⟩
      by_cases hND : ∀ q ∈ traceQueries P (evs ++ [.spend tx g]) s', ¬ q.degenerate
      swap
      · left; right; left; push Not at hND
        obtain ⟨q, hq, hd⟩ := hND
        exact ⟨q, List.mem_append_left _ hq, hd⟩
      rcases c3 P hC1 evs s tx g s' hrun hs with hb | ⟨hR, hkeys, hroot, -⟩
      · left; exact hb
      right
      obtain ⟨hin, -⟩ := core P evs s s' tx g hrun hinv hs hNC hND hR hkeys hroot
      have hnk := nf_key P tx hs.1 hR hkeys
      set sd := settleData tx with hsd
      set w := witOf (extOf P tx) with hw
      have hs1 : BInv P (evs ++ [.spend tx g])
          { s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf sd w,
                   balance := s.balance - g } := by
        refine ⟨base1, fun o ho => ?_⟩
        rcases List.mem_append.1 ho with ho | ho
        · exact spentOK_mono P evs _ s _ o (Qe_mono P evs _) (fun e => List.prefix_refl _)
            (fun x hx => List.mem_append_left _ hx) (hinv.2 o ho)
        · unfold inputsOf at ho
          simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
            decide_eq_true_eq] at ho
          obtain ⟨k, hk, rfl⟩ := ho
          obtain ⟨hlt, hL, -, -⟩ := hin k hk
          obtain ⟨w1, w2, w3, -⟩ := mem_witnessQueries_k (stmtOf (extOf P tx)) w k
          refine ⟨hlt, w.sk k, w.ρ k, w.v k, hL, wq_in_Qe P evs tx g _ w1, wq_in_Qe P evs tx g _ w2,
            wq_in_Qe P evs tx g _ w3, ?_⟩
          show (nf (D P.c P.A sd.epoch) (w.sk k) ((s.leaves sd.epoch).getD (w.idx k) 0)
            (w.idx k)).val ∈ s.keys ++ tx.nonceKeys
          rw [hL]; exact List.mem_append_right _ (hnk k)
      have hnew : ∀ x ∈ newLeaves sd w, LeafOK P (evs ++ [.spend tx g]) x.1 x.2 := by
        obtain ⟨-, -, -, -, ho1, ho2, hrange, -⟩ := hR
        simp only [stmtOfTx, SettleData.stmt] at ho1 ho2
        have hov0 : (w.ov 0).val < 2 ^ 128 := hrange _ (by simp)
        have hov1 : (w.ov 1).val < 2 ^ 128 := hrange _ (by simp)
        obtain ⟨oq0, oq1⟩ := out_mem (stmtOf (extOf P tx)) w
        have g0 : LeafOK P (evs ++ [.spend tx g]) (sd.o1 : F) (w.ov 0).val :=
          ⟨hov0, w.oi 0, by rw [ZMod.natCast_zmod_val]; exact ho1,
           by rw [ZMod.natCast_zmod_val]; exact wq_in_Qe P evs tx g _ oq0⟩
        have g1 : LeafOK P (evs ++ [.spend tx g]) (sd.o2 : F) (w.ov 1).val :=
          ⟨hov1, w.oi 1, by rw [ZMod.natCast_zmod_val]; exact ho2,
           by rw [ZMod.natCast_zmod_val]; exact wq_in_Qe P evs tx g _ oq1⟩
        intro x hx
        have hx' : x = ((sd.o1 : F), (w.ov 0).val) ∨ x = ((sd.o2 : F), (w.ov 1).val) := by
          unfold newLeaves at hx; split_ifs at hx <;> simp at hx <;> tauto
        rcases hx' with rfl | rfl
        · exact g0
        · exact g1
      have hs2 : BInv P (evs ++ [.spend tx g])
          (({ s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf sd w,
                     balance := s.balance - g } : PoolState).append (newLeaves sd w)) := by
        obtain ⟨hk, hsp⟩ := append_keys_spent
          ({ s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf sd w,
                     balance := s.balance - g } : PoolState) (newLeaves sd w)
        refine ⟨f2_append _ _ _ hs1.1 hnew, fun o ho => ?_⟩
        rw [hsp] at ho
        exact spentOK_mono P _ _ _ _ o (fun q hq => hq) (grows_append _ _).leaves
          (fun x hx => by rw [hk]; exact hx) (hs1.2 o ho)
      obtain ⟨-, -, -, -, -, -, -, hs'⟩ := hs
      subst hs'
      split_ifs
      · exact hs2
      · exact hs2
      · exact hs1

theorem c5b (P : Pool) (hC1 : C1) : C5b P := by
  intro evs s tx g s' hrun hs
  rcases binv_run P hC1 evs s hrun with hb | hinv
  · left; exact bad_mono P (List.prefix_append _ _) (grows_step P s s' _ hs) [] hb
  by_cases hNC : NoColl (traceQueries P (evs ++ [.spend tx g]) s')
  swap
  · left; left; unfold NoColl at hNC; push Not at hNC
    obtain ⟨q1, h1, q2, h2, hc⟩ := hNC
    exact ⟨q1, List.mem_append_left _ h1, q2, List.mem_append_left _ h2, hc⟩
  by_cases hND : ∀ q ∈ traceQueries P (evs ++ [.spend tx g]) s', ¬ q.degenerate
  swap
  · left; right; left; push Not at hND
    obtain ⟨q, hq, hd⟩ := hND
    exact ⟨q, List.mem_append_left _ hq, hd⟩
  rcases c3 P hC1 evs s tx g s' hrun hs with hb | ⟨hR, hkeys, hroot, -⟩
  · left; exact hb
  right
  exact core P evs s s' tx g hrun hinv hs hNC hND hR hkeys hroot

theorem c5i (P : Pool) (hC1 : C1) : C5i P := c5i_of P (c5b P hC1)
theorem c5c (P : Pool) (hC1 : C1) : C5c P := c5c_of P hC1 (c5b P hC1)
theorem c4 (P : Pool) (hC1 : C1) : C4 P := c4_of P hC1 (c5b P hC1) (c5c P hC1)


end
end MSP
