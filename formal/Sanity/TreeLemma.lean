import Spec
import Mathlib.Tactic.Ring

/-! The tree lemma Spendable's R3 needs,
`MR (L.getD i 0) i (siblingsOf L i) = TR L` for `i < 2 ^ DEPTH`, proven in full.
It needs neither `i < L.length` nor `L.length ≤ 2 ^ DEPTH`. -/

namespace MSP
noncomputable section
open Classical

/-- `treeRoot h` reads only the first `2 ^ h` leaves. -/
theorem treeRoot_take (h : ℕ) (L : List F) : treeRoot h (L.take (2 ^ h)) = treeRoot h L := by
  induction h generalizing L with
  | zero => cases L <;> rfl
  | succ h ih =>
    simp only [treeRoot]
    congr 1
    · rw [List.take_take, Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ h))]
    · rw [List.drop_take, pow_succ, show 2 ^ h * 2 - 2 ^ h = 2 ^ h by omega, ih]

theorem xor_one_even (j : ℕ) : (2 * j) ^^^ 1 = 2 * j + 1 := by
  apply Nat.eq_of_testBit_eq; intro n
  rw [Nat.testBit_xor]
  cases n with
  | zero => simp [Nat.testBit_zero]
  | succ n =>
    simp only [Nat.testBit_succ]
    rw [show 2 * j / 2 = j by omega, show (2 * j + 1) / 2 = j by omega]
    simp

theorem xor_one_odd (j : ℕ) : (2 * j + 1) ^^^ 1 = 2 * j := by
  apply Nat.eq_of_testBit_eq; intro n
  rw [Nat.testBit_xor]
  cases n with
  | zero => simp [Nat.testBit_zero]
  | succ n =>
    simp only [Nat.testBit_succ]
    rw [show 2 * j / 2 = j by omega, show (2 * j + 1) / 2 = j by omega]
    simp

/-- The subtree of height `l` holding leaf `i`, and its sibling. -/
def blk (L : List F) (l m : ℕ) : List F := (L.drop (m * 2 ^ l)).take (2 ^ l)

theorem blk_left (L : List F) (l j : ℕ) : (blk L (l + 1) j).take (2 ^ l) = blk L l (2 * j) := by
  simp only [blk, List.take_take]
  rw [Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ l)), pow_succ]
  congr 2; ring

theorem blk_right (L : List F) (l j : ℕ) : (blk L (l + 1) j).drop (2 ^ l) = blk L l (2 * j + 1) := by
  simp only [blk, List.drop_take, List.drop_drop]
  rw [pow_succ, show 2 ^ l * 2 - 2 ^ l = 2 ^ l by omega]
  congr 2; ring

def sibN (L : List F) (i l : ℕ) : F := treeRoot l (blk L l ((i / 2 ^ l) ^^^ 1))

def stepN (L : List F) (i : ℕ) (cur : F) (l : ℕ) : F :=
  if i.testBit l then H2 (sibN L i l) cur else H2 cur (sibN L i l)

theorem headD_drop_take (L : List F) (i : ℕ) : ((L.drop i).take 1).headD 0 = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp
  | cons a t ih => cases i with
    | zero => rfl
    | succ i => simpa using ih i

theorem fold_inv (L : List F) (i n : ℕ) :
    (List.range n).foldl (stepN L i) (L.getD i 0) = treeRoot n (blk L n (i / 2 ^ n)) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.div_one, blk, mul_one, treeRoot]
    exact (headD_drop_take L i).symm
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    set j := i / 2 ^ (n + 1)
    have hm : i / 2 ^ n = 2 * j + (i / 2 ^ n) % 2 := by
      have : i / 2 ^ n / 2 = j := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
      omega
    have hbit : i.testBit n = true ↔ (i / 2 ^ n) % 2 = 1 := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]; simp [Nat.one_and_eq_mod_two]
    show stepN L i _ n = _
    simp only [treeRoot, blk_left, blk_right, stepN, sibN]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ n) with h0 | h1
    · have hb : i.testBit n = false := by
        cases hh : i.testBit n
        · rfl
        · exact absurd (hbit.mp hh) (by omega)
      rw [hb, hm, h0, Nat.add_zero, xor_one_even]
      simp
    · have hb : i.testBit n = true := hbit.mpr h1
      rw [hb, hm, h1, xor_one_odd]
      simp

theorem MR_eq_foldN (leaf : F) (L : List F) (i : ℕ) :
    MR leaf i (siblingsOf L i) = (List.range DEPTH).foldl (stepN L i) leaf := by
  unfold MR
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  rfl

/-- The tree lemma. -/
theorem MR_siblingsOf (L : List F) (i : ℕ) (hi : i < 2 ^ DEPTH) :
    MR (L.getD i 0) i (siblingsOf L i) = TR L := by
  rw [MR_eq_foldN, fold_inv, Nat.div_eq_of_lt hi]
  simp only [blk, zero_mul, List.drop_zero, TR]
  exact treeRoot_take DEPTH L

#print axioms MR_siblingsOf

/-- Spendable's R3, in the exact form round 6's `mkSpend_R` takes as `hR3`. -/
theorem spendable_R3 (P : Pool) (e : ℕ) (Ls : List F) (n i : ℕ) (sk ρ v skd ρd f rcp auth : F)
    (hi : i < n) (hcap : i < 2 ^ DEPTH) (hleaf : Ls.getD i 0 = cm (inner sk ρ) v) :
    v ≠ 0 → MR ((mkSpend P e (Ls.take n) i sk ρ v skd ρd f rcp auth).2.leaf 0) i
      (siblingsOf (Ls.take n) i) = TR (Ls.take n) := by
  intro _
  have h := MR_siblingsOf (Ls.take n) i hcap
  have hg : (Ls.take n).getD i 0 = cm (inner sk ρ) v := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD, hleaf]
  rw [hg] at h
  simpa [mkSpend, Witness.leaf] using h

#print axioms spendable_R3

end
end MSP
