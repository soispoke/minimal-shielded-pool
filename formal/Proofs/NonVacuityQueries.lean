import Spec.Main
import Mathlib.Tactic

/-! Exact compact query support for W1's finite non-vacuity check. Empty
subtrees are represented once per height instead of expanded into all their
nodes. These are symbolic equivalences, not assumptions about hash security
or a proof of W1. -/

namespace MSP.NonVacuity

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The distinct levels used by an empty subtree; equal queries at different
levels are deliberately retained, so no injectivity is needed. -/
def emptyQueries : ℕ → List Query
  | 0 => []
  | h + 1 => emptyQueries h ++ [.h2 (Z h) (Z h)]

theorem emptyQueries_length (h : ℕ) : (emptyQueries h).length = h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [emptyQueries, List.length_append, List.length_singleton, ih]

theorem treeRoot_nil (h : ℕ) : treeRoot h [] = Z h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [treeRoot, List.take_nil, List.drop_nil, ih, Z]

theorem emptyQueries_mem (h : ℕ) (q : Query) :
    q ∈ emptyQueries h ↔ q ∈ treeQueries h [] := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [emptyQueries, treeQueries, List.take_nil, List.drop_nil, treeRoot_nil,
      List.mem_append, List.mem_singleton, ← ih, or_self]

/-- Compute the exact root and a query support list together, pruning empty
subtrees before either roots or queries are recursively evaluated. -/
def compactTree : ℕ → List F → F × List Query
  | 0, L => (L.headD 0, [])
  | h + 1, [] => (Z (h + 1), emptyQueries (h + 1))
  | h + 1, a :: L =>
      let left := compactTree h ((a :: L).take (2 ^ h))
      let right := compactTree h ((a :: L).drop (2 ^ h))
      (H2 left.1 right.1, left.2 ++ right.2 ++ [.h2 left.1 right.1])

def compactRoot (h : ℕ) (L : List F) : F := (compactTree h L).1
def compactQueries (h : ℕ) (L : List F) : List Query := (compactTree h L).2

/-- Pruning preserves the exact root, independently of all hash properties. -/
theorem compactRoot_eq (h : ℕ) (L : List F) : compactRoot h L = treeRoot h L := by
  induction h generalizing L with
  | zero => rfl
  | succ h ih =>
    cases L with
    | nil => exact (treeRoot_nil (h + 1)).symm
    | cons a L =>
      change H2 (compactRoot h ((a :: L).take (2 ^ h)))
        (compactRoot h ((a :: L).drop (2 ^ h))) = _
      rw [ih, ih]
      rfl

/-- Membership is equivalent, including when distinct inputs happen to hash
to the same output. Only duplicate occurrences are removed. -/
theorem compactQueries_mem (h : ℕ) (L : List F) (q : Query) :
    q ∈ compactQueries h L ↔ q ∈ treeQueries h L := by
  induction h generalizing L with
  | zero => rfl
  | succ h ih =>
    cases L with
    | nil => exact emptyQueries_mem (h + 1) q
    | cons a L =>
      change q ∈ compactQueries h ((a :: L).take (2 ^ h)) ++
        compactQueries h ((a :: L).drop (2 ^ h)) ++
        [.h2 (compactRoot h ((a :: L).take (2 ^ h)))
          (compactRoot h ((a :: L).drop (2 ^ h)))] ↔ _
      simp only [treeQueries, List.mem_append, List.mem_singleton, ih, compactRoot_eq]

theorem compactQueries_nil (h : ℕ) : compactQueries h [] = emptyQueries h := by
  cases h <;> rfl

/-- At depth 20 an empty tree requires only 20 query occurrences. -/
theorem compactQueries_nil_length (h : ℕ) : (compactQueries h []).length = h := by
  rw [compactQueries_nil, emptyQueries_length]

theorem compactQueries_singleton_succ (h : ℕ) (leaf : F) :
    (compactQueries (h + 1) [leaf]).length =
      (compactQueries h [leaf]).length + h + 1 := by
  have hp : 0 < 2 ^ h := by positivity
  have ht : ([leaf] : List F).take (2 ^ h) = [leaf] := by
    apply List.take_of_length_le
    change 1 ≤ 2 ^ h
    omega
  have hd : ([leaf] : List F).drop (2 ^ h) = [] := by
    apply List.drop_eq_nil_of_le
    change 1 ≤ 2 ^ h
    omega
  change ((compactTree h ([leaf].take (2 ^ h))).2 ++
    (compactTree h ([leaf].drop (2 ^ h))).2 ++ [_]).length = _
  rw [ht, hd]
  simp only [List.length_append, List.length_singleton]
  change (compactQueries h [leaf]).length + (compactQueries h []).length + 1 = _
  rw [compactQueries_nil_length]

/-- A one-leaf tree has triangular, rather than exponential, query support. -/
theorem compactQueries_singleton_length (h : ℕ) (leaf : F) :
    2 * (compactQueries h [leaf]).length = h * (h + 1) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [compactQueries_singleton_succ]
    calc
      2 * ((compactQueries h [leaf]).length + h + 1) =
          2 * (compactQueries h [leaf]).length + 2 * h + 2 := by ring
      _ = (h + 1) * (h + 1 + 1) := by rw [ih]; ring

theorem compactQueries_depth_singleton_length (leaf : F) :
    (compactQueries DEPTH [leaf]).length = 210 := by
  have h := compactQueries_singleton_length DEPTH leaf
  change 2 * (compactQueries DEPTH [leaf]).length = 420 at h
  omega

/-- The unpruned specification enumerates every internal node, regardless
of the number of supplied leaves. -/
theorem treeQueries_length_add_one (h : ℕ) (L : List F) :
    (treeQueries h L).length + 1 = 2 ^ h := by
  induction h generalizing L with
  | zero => rfl
  | succ h ih =>
    simp only [treeQueries, List.length_append, List.length_singleton]
    have hl := ih (L.take (2 ^ h))
    have hr := ih (L.drop (2 ^ h))
    rw [pow_succ]
    omega

theorem treeQueries_depth_length (L : List F) :
    (treeQueries DEPTH L).length = 1048575 := by
  have h := treeQueries_length_add_one DEPTH L
  change (treeQueries DEPTH L).length + 1 = 1048576 at h
  omega

/-- The original predicate is checked on precisely the compact query support,
not by a global injectivity or collision-resistance premise. -/
theorem tree_collision_iff (h : ℕ) (L : List F) :
    (∃ q₁ ∈ treeQueries h L, ∃ q₂ ∈ treeQueries h L, q₁.collide q₂) ↔
      (∃ q₁ ∈ compactQueries h L, ∃ q₂ ∈ compactQueries h L, q₁.collide q₂) := by
  simp only [compactQueries_mem]

theorem tree_degenerate_iff (h : ℕ) (L : List F) :
    (∃ q ∈ treeQueries h L, q.degenerate) ↔
      (∃ q ∈ compactQueries h L, q.degenerate) := by
  simp only [compactQueries_mem]

end MSP.NonVacuity
