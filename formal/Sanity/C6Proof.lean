import Sanity.TreeLemma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! C6's third conjunct is provable from Tree.lean's definitions,
given only its first conjunct (`zeroConst l = Z l` for `l < DEPTH`), which
`c6consts.py` checks against `reference/poseidon_bn254.py`. So `insertLoop`'s
fuel (`DEPTH + 1`) and `zeroConst`'s indexing are right. -/

namespace MSP
noncomputable section
open Classical

theorem treeRoot_nil (h : ℕ) : treeRoot h [] = Z h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [treeRoot, Z, ih]

theorem blk_split (L : List F) (l j : ℕ) :
    treeRoot (l + 1) (blk L (l + 1) j) = H2 (treeRoot l (blk L l (2 * j))) (treeRoot l (blk L l (2 * j + 1))) := by
  simp only [treeRoot, blk, List.take_take, List.drop_take, List.drop_drop]
  rw [Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ l)), pow_succ,
      show 2 ^ l * 2 - 2 ^ l = 2 ^ l by omega]
  congr 4 <;> ring

/-- A block inside `L` is unchanged by appending. -/
theorem blk_append (L M : List F) (l k : ℕ) (h : (k + 1) * 2 ^ l ≤ L.length) :
    blk (L ++ M) l k = blk L l k := by
  have h' : k * 2 ^ l + 2 ^ l ≤ L.length := by linarith [add_mul k 1 (2 ^ l)]
  simp only [blk]
  rw [List.drop_append_of_le_length (le_trans (Nat.le_add_right _ _) h'), List.take_append_of_le_length]
  rw [List.length_drop]; omega

/-- A block past the end of `L` is empty. -/
theorem blk_past (L : List F) (l k : ℕ) (h : L.length ≤ k * 2 ^ l) : blk L l k = [] := by
  simp [blk, List.drop_eq_nil_of_le h]

theorem low_ones (n B : ℕ) (hB : 0 < B) (hmod : (n + 1) % B = 0) : n % B + 1 = B := by
  have hlt := Nat.mod_lt n hB
  rw [Nat.add_mod] at hmod
  rcases Nat.lt_or_ge 1 B with h | h
  · rw [Nat.mod_eq_of_lt h] at hmod
    by_contra hne
    rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
  · have : B = 1 := by omega
    subst this; omega

theorem div_pow_succ (n l : ℕ) : n / 2 ^ (l + 1) = n / 2 ^ l / 2 := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- The block of level `m` just before `n`'s lies inside a list of length `n`. -/
theorem prev_blk_le (n m : ℕ) (hodd : n / 2 ^ m % 2 = 1) : (n / 2 ^ m - 1 + 1) * 2 ^ m ≤ n := by
  have h1 : 1 ≤ n / 2 ^ m := by generalize n / 2 ^ m = x at hodd ⊢; omega
  rw [Nat.sub_add_cancel h1]; exact Nat.div_mul_le_self n (2 ^ m)

private def Inv (L : List F) (t : LogicTree) : Prop :=
  t.next = L.length ∧
  ∀ m, (L.length / 2 ^ m) % 2 = 1 → t.filled m = treeRoot m (blk L m (L.length / 2 ^ m - 1))

theorem loop (L : List F) (c : F) (filled : ℕ → F)
    (hI : ∀ m, (L.length / 2 ^ m) % 2 = 1 → filled m = treeRoot m (blk L m (L.length / 2 ^ m - 1))) :
    ∀ fuel l node, L.length / 2 ^ l < 2 ^ fuel → (L.length + 1) % 2 ^ l = 0 →
      node = treeRoot l (blk (L ++ [c]) l (L.length / 2 ^ l)) →
      ∃ t, (L.length / 2 ^ t) % 2 = 0 ∧ (L.length + 1) % 2 ^ t = 0 ∧
        insertLoop filled node (L.length / 2 ^ l) l fuel =
          Function.update filled t (treeRoot t (blk (L ++ [c]) t (L.length / 2 ^ t))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l node hlt hmod hnode
    refine ⟨l, by rw [pow_zero] at hlt; generalize L.length / 2 ^ l = x at hlt ⊢; omega, hmod, ?_⟩
    simp [insertLoop, hnode]
  | succ fuel ih =>
    intro l node hlt hmod hnode
    by_cases hb : L.length / 2 ^ l % 2 = 1
    · simp only [insertLoop, hb, ite_true]
      rw [← div_pow_succ]
      apply ih (l + 1)
      · rw [div_pow_succ, Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hlt; exact hlt
      · have h1 := Nat.div_add_mod L.length (2 ^ l)
        have h3 := low_ones L.length (2 ^ l) (Nat.two_pow_pos l) hmod
        have hodd : L.length / 2 ^ l = 2 * (L.length / 2 ^ l / 2) + 1 := by omega
        have : L.length + 1 = 2 ^ (l + 1) * (L.length / 2 ^ l / 2 + 1) := by
          rw [pow_succ]; rw [hodd] at h1; nlinarith
        rw [this]; exact Nat.mul_mod_right _ _
      · rw [hnode, blk_split, div_pow_succ]
        have hodd : L.length / 2 ^ l = 2 * (L.length / 2 ^ l / 2) + 1 := by omega
        rw [← hodd, hI l hb, show 2 * (L.length / 2 ^ l / 2) = L.length / 2 ^ l - 1 by omega]
        congr 2
        exact (blk_append L [c] l _ (prev_blk_le _ _ hb)).symm
    · refine ⟨l, by omega, hmod, ?_⟩
      simp [insertLoop, hb, hnode]

theorem insert_inv (L : List F) (t : LogicTree) (c : F) (hI : Inv L t) (hcap : L.length < CAPACITY) :
    Inv (L ++ [c]) (t.insert c) := by
  obtain ⟨hnext, hf⟩ := hI
  obtain ⟨T, hT0, hTmod, hT⟩ := loop L c t.filled hf (DEPTH + 1) 0 c
    (by simp only [pow_zero, Nat.div_one]; unfold CAPACITY at hcap; rw [pow_succ]; omega)
    (by rw [pow_zero, Nat.mod_one])
    (by simp only [pow_zero, blk, mul_one, treeRoot]; rw [headD_drop_take]; simp)
  refine ⟨by simp [LogicTree.insert, hnext], ?_⟩
  intro m hm
  simp only [LogicTree.insert, hnext]
  simp only [pow_zero, Nat.div_one] at hT
  rw [hT]
  simp only [List.length_append, List.length_singleton] at hm ⊢
  set n := L.length with hn
  set j := n / 2 ^ T / 2 with hj
  have hq : n / 2 ^ T = 2 * j := by omega
  have hr := low_ones n (2 ^ T) (Nat.two_pow_pos T) hTmod
  have hn1 : n + 1 = 2 ^ T * (2 * j + 1) := by
    have h1 := Nat.div_add_mod n (2 ^ T); rw [hq] at h1; nlinarith
  rcases lt_trichotomy m T with hlt | rfl | hgt
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    rw [hn1, hk, show m + k + 1 = m + (k + 1) by omega, pow_add, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos m), pow_succ] at hm
    rw [show 2 ^ k * 2 * (2 * j + 1) = 2 * (2 ^ k * (2 * j + 1)) by ring] at hm
    omega
  · rw [Function.update_self, hn1, Nat.mul_div_cancel_left _ (Nat.two_pow_pos m), hq]
    simp
  · rw [Function.update_of_ne (by omega)]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
    have hdiv : (n + 1) / 2 ^ m = n / 2 ^ m := by
      have e1 : (n + 1) / 2 ^ m = (2 * j + 1) / 2 ^ (k + 1) := by
        rw [hk, show T + k + 1 = T + (k + 1) by omega, pow_add, ← Nat.div_div_eq_div_mul, hn1,
            Nat.mul_div_cancel_left _ (Nat.two_pow_pos T)]
      have e2 : n / 2 ^ m = (2 * j) / 2 ^ (k + 1) := by
        rw [hk, show T + k + 1 = T + (k + 1) by omega, pow_add, ← Nat.div_div_eq_div_mul, hq]
      rw [e1, e2, pow_succ, mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      congr 1; omega
    rw [hdiv] at hm ⊢
    rw [hf m hm, blk_append L [c] m _ (prev_blk_le _ _ hm)]

theorem foldl_inv : ∀ L : List F, L.length ≤ CAPACITY → Inv L (L.foldl LogicTree.insert LogicTree.empty) := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; refine ⟨rfl, fun m hm => ?_⟩; simp at hm
  | append_singleton L c ih =>
    intro h
    rw [List.length_append, List.length_singleton] at h
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact insert_inv L _ c (ih (by omega)) (by omega)

theorem root_eq (L : List F) (t : LogicTree) (hz : ∀ l < DEPTH, zeroConst l = Z l)
    (hI : Inv L t) (hcap : L.length ≤ CAPACITY) : t.root = TR L := by
  obtain ⟨hnext, hf⟩ := hI
  unfold LogicTree.root
  split_ifs with hfull
  · rw [hnext] at hfull
    have h1 : L.length / 2 ^ DEPTH = 1 := by rw [hfull]; simp [CAPACITY]
    rw [hf DEPTH (by rw [h1]), h1]
    simp [blk, TR, treeRoot_take]
  · rw [hnext] at hfull ⊢
    have hlt : L.length < 2 ^ DEPTH := by unfold CAPACITY at hcap hfull; omega
    have key : ∀ k ≤ DEPTH, (List.range k).foldl
        (fun (acc : F × ℕ) l =>
          (if acc.2 % 2 = 0 then H2 acc.1 (zeroConst l) else H2 (t.filled l) acc.1, acc.2 / 2))
        (0, L.length) = (treeRoot k (blk L k (L.length / 2 ^ k)), L.length / 2 ^ k) := by
      intro k
      induction k with
      | zero =>
        intro _
        simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.div_one, blk, mul_one, treeRoot]
        rw [headD_drop_take]; simp
      | succ k ih =>
        intro hk
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
        simp only
        rw [div_pow_succ, blk_split]
        split_ifs with he
        · have hq : 2 * (L.length / 2 ^ k / 2) = L.length / 2 ^ k := by omega
          have hpast : L.length ≤ (2 * (L.length / 2 ^ k / 2) + 1) * 2 ^ k := by
            have := Nat.lt_div_mul_add (a := L.length) (Nat.two_pow_pos k)
            rw [hq, add_mul, one_mul]; exact le_of_lt this
          rw [blk_past L k _ hpast, hq, treeRoot_nil, hz k (by omega)]
        · have hodd : L.length / 2 ^ k = 2 * (L.length / 2 ^ k / 2) + 1 := by omega
          rw [hf k (by omega), ← hodd, show 2 * (L.length / 2 ^ k / 2) = L.length / 2 ^ k - 1 by omega]
    rw [key DEPTH le_rfl, Nat.div_eq_of_lt hlt]
    simp [blk, TR, treeRoot_take]

theorem C6_third (hz : ∀ l < DEPTH, zeroConst l = Z l) :
    ∀ L : List F, L.length ≤ CAPACITY → (L.foldl LogicTree.insert LogicTree.empty).root = TR L :=
  fun L h => root_eq L _ hz (foldl_inv L h) h

#print axioms C6_third

end
end MSP
