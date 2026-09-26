import Proofs.C5cC4
import Sanity.TreeLemma

/-! The path walk: a Merkle path whose root equals `TR L`, with no collision
between its queries and `treeQueries DEPTH L`, starts at `L.getD i 0`. -/

namespace MSP
noncomputable section
open Classical

def NoColl (T : List Query) : Prop := ∀ q1 ∈ T, ∀ q2 ∈ T, ¬ q1.collide q2

theorem h2_inj {T : List Query} (h : NoColl T) {a b a' b' : F}
    (h1 : Query.h2 a b ∈ T) (h2 : Query.h2 a' b' ∈ T) (he : H2 a b = H2 a' b') : a = a' ∧ b = b' := by
  by_contra hne
  exact h _ h1 _ h2 ⟨fun hh => hne (by simpa using hh), he⟩

theorem h3_inj {T : List Query} (h : NoColl T) {a b c a' b' c' : F}
    (h1 : Query.h3 a b c ∈ T) (h2 : Query.h3 a' b' c' ∈ T) (he : H3 a b c = H3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  by_contra hne
  exact h _ h1 _ h2 ⟨fun hh => hne (by simpa using hh), he⟩

def sibE (sib : Fin DEPTH → F) (l : ℕ) : F := if h : l < DEPTH then sib ⟨l, h⟩ else 0

def pstep (i : ℕ) (sib : ℕ → F) (acc : F × List Query) (l : ℕ) : F × List Query :=
  if i.testBit l then (H2 (sib l) acc.1, acc.2 ++ [Query.h2 (sib l) acc.1])
  else (H2 acc.1 (sib l), acc.2 ++ [Query.h2 acc.1 (sib l)])

def pfold (leaf : F) (i : ℕ) (sib : ℕ → F) (m : ℕ) : F × List Query :=
  (List.range m).foldl (pstep i sib) (leaf, [])

theorem pathQueries_eq (leaf : F) (i : ℕ) (sib : Fin DEPTH → F) :
    pathQueries leaf i sib = (pfold leaf i (sibE sib) DEPTH).2 := by
  unfold pathQueries pfold
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 2
  funext acc l
  simp [pstep, sibE, l.isLt]

theorem fst_foldl (i : ℕ) (sib : ℕ → F) (ls : List ℕ) (c : F) (qs : List Query) :
    (ls.foldl (pstep i sib) (c, qs)).1 =
      ls.foldl (fun cur l => if i.testBit l then H2 (sib l) cur else H2 cur (sib l)) c := by
  induction ls generalizing c qs with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [show pstep i sib (c, qs) a = ((if i.testBit a then H2 (sib a) c else H2 c (sib a)),
        (pstep i sib (c, qs) a).2) by unfold pstep; split_ifs <;> rfl]
    exact ih _ _

theorem MR_eq_pfold (leaf : F) (i : ℕ) (sib : Fin DEPTH → F) :
    MR leaf i sib = (pfold leaf i (sibE sib) DEPTH).1 := by
  unfold pfold
  rw [fst_foldl]
  unfold MR
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext cur l
  simp [sibE, l.isLt]

theorem pfold_succ (leaf : F) (i : ℕ) (sib : ℕ → F) (m : ℕ) :
    pfold leaf i sib (m + 1) = pstep i sib (pfold leaf i sib m) m := by
  simp [pfold, List.range_succ, List.foldl_append]

theorem pfold_prefix (leaf : F) (i : ℕ) (sib : ℕ → F) (m d : ℕ) :
    (pfold leaf i sib m).2 <+: (pfold leaf i sib (m + d)).2 := by
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine ih.trans ?_
    rw [← Nat.add_assoc, pfold_succ]
    unfold pstep; split_ifs <;> exact List.prefix_append _ _

/-- the path query at level `l` -/
def pq (leaf : F) (i : ℕ) (sib : ℕ → F) (l : ℕ) : Query :=
  if i.testBit l then Query.h2 (sib l) (pfold leaf i sib l).1
  else Query.h2 (pfold leaf i sib l).1 (sib l)

theorem pq_mem (leaf : F) (i : ℕ) (sib : ℕ → F) (l m : ℕ) (hl : l < m) :
    pq leaf i sib l ∈ (pfold leaf i sib m).2 := by
  obtain ⟨d, rfl⟩ : ∃ d, m = l + 1 + d := ⟨m - (l + 1), by omega⟩
  apply (pfold_prefix leaf i sib (l + 1) d).subset
  rw [pfold_succ]; unfold pstep pq; split_ifs <;> simp

theorem treeQueries_take (h : ℕ) (L : List F) : treeQueries h (L.take (2 ^ h)) = treeQueries h L := by
  induction h generalizing L with
  | zero => rfl
  | succ h ih =>
    simp only [treeQueries]
    have e1 : (L.take (2 ^ (h + 1))).take (2 ^ h) = L.take (2 ^ h) := by
      rw [List.take_take, Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ h))]
    have e2 : (L.take (2 ^ (h + 1))).drop (2 ^ h) = (L.drop (2 ^ h)).take (2 ^ h) := by
      rw [List.drop_take, pow_succ, show 2 ^ h * 2 - 2 ^ h = 2 ^ h by omega]
    rw [e1, e2, ih (L.drop (2 ^ h)), treeRoot_take h (L.drop (2 ^ h))]

theorem tq_blk (L : List F) (l j : ℕ) :
    treeQueries (l + 1) (blk L (l + 1) j) =
      treeQueries l (blk L l (2 * j)) ++ treeQueries l (blk L l (2 * j + 1)) ++
      [Query.h2 (treeRoot l (blk L l (2 * j))) (treeRoot l (blk L l (2 * j + 1)))] := by
  simp only [treeQueries, blk_left, blk_right]

theorem tr_blk (L : List F) (l j : ℕ) :
    treeRoot (l + 1) (blk L (l + 1) j) =
      H2 (treeRoot l (blk L l (2 * j))) (treeRoot l (blk L l (2 * j + 1))) := by
  simp only [treeRoot, blk_left, blk_right]

theorem div_split (i l : ℕ) : i / 2 ^ l = 2 * (i / 2 ^ (l + 1)) + (i / 2 ^ l) % 2 := by
  have : i / 2 ^ l / 2 = i / 2 ^ (l + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  omega

theorem bit_iff (i l : ℕ) : i.testBit l = true ↔ (i / 2 ^ l) % 2 = 1 := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]; simp [Nat.one_and_eq_mod_two]

theorem tq_sub (L : List F) (i : ℕ) (hi : i < 2 ^ DEPTH) :
    ∀ d l, l + d = DEPTH → ∀ q ∈ treeQueries l (blk L l (i / 2 ^ l)), q ∈ treeQueries DEPTH L := by
  intro d
  induction d with
  | zero =>
    intro l hl q hq
    simp only [Nat.add_zero] at hl; subst hl
    rw [Nat.div_eq_of_lt hi] at hq
    simpa [blk, treeQueries_take] using hq
  | succ d ih =>
    intro l hl q hq
    apply ih (l + 1) (by omega)
    rw [tq_blk]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ l) with h0 | h1
    · rw [div_split i l, h0, Nat.add_zero] at hq
      simp [hq]
    · rw [div_split i l, h1] at hq
      simp [hq]

theorem path_walk (T : List Query) (hNC : NoColl T)
    (leaf : F) (i : ℕ) (sib : Fin DEPTH → F) (L : List F) (hi : i < 2 ^ DEPTH)
    (hp : ∀ q ∈ pathQueries leaf i sib, q ∈ T) (ht : ∀ q ∈ treeQueries DEPTH L, q ∈ T)
    (hr : MR leaf i sib = TR L) : leaf = L.getD i 0 := by
  set sb := sibE sib
  have walk : ∀ d l, l + d = DEPTH →
      (pfold leaf i sb l).1 = treeRoot l (blk L l (i / 2 ^ l)) := by
    intro d
    induction d with
    | zero =>
      intro l hl
      simp only [Nat.add_zero] at hl; subst hl
      rw [← MR_eq_pfold, hr, Nat.div_eq_of_lt hi]
      simp [blk, TR, treeRoot_take]
    | succ d ih =>
      intro l hl
      have ih1 := ih (l + 1) (by omega)
      set j := i / 2 ^ (l + 1)
      have hpq : pq leaf i sb l ∈ T := by
        apply hp; rw [pathQueries_eq]; exact pq_mem leaf i sb l DEPTH (by omega)
      have htq : Query.h2 (treeRoot l (blk L l (2 * j))) (treeRoot l (blk L l (2 * j + 1))) ∈ T := by
        apply ht
        apply tq_sub L i hi d (l + 1) (by omega)
        rw [tq_blk]; exact List.mem_append_right _ (List.mem_singleton_self _)
      rw [pfold_succ, tr_blk] at ih1
      unfold pstep at ih1
      unfold pq at hpq
      have hsplit := div_split i l
      rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ l) with h0 | h1
      · have hb : i.testBit l = false := by
          cases hh : i.testBit l
          · rfl
          · exact absurd ((bit_iff i l).mp hh) (by omega)
        simp only [hb, ite_false, Bool.false_eq_true] at ih1 hpq
        have := h2_inj hNC hpq htq ih1
        rw [this.1, hsplit, h0, Nat.add_zero]
      · have hb : i.testBit l = true := (bit_iff i l).mpr h1
        simp only [hb, ite_true] at ih1 hpq
        have := h2_inj hNC hpq htq ih1
        rw [this.2, hsplit, h1]
  have h0 := walk DEPTH 0 (by omega)
  simp only [pfold, List.range_zero, List.foldl_nil, pow_zero, Nat.div_one, treeRoot, blk, mul_one] at h0
  rw [h0, headD_drop_take]

#print axioms path_walk

end
end MSP
