import Spec.Hash

/-!
# D10: a valid spend
-/

namespace MSP

/-- D10. The private witness of a spend: for each input `k`, its key, `ρ`,
value, index and siblings; for each output, its `inner` and value. -/
structure Witness where
  sk : Fin 2 → F
  ρ : Fin 2 → F
  v : Fin 2 → F
  idx : Fin 2 → ℕ
  sib : Fin 2 → Fin DEPTH → F
  oi : Fin 2 → F
  ov : Fin 2 → F
deriving Inhabited

def Witness.leaf (w : Witness) (k : Fin 2) : F := cm (inner (w.sk k) (w.ρ k)) (w.v k)

/-- D10, R1 to R9. -/
def R (x : Statement) (w : Witness) : Prop :=
  -- R1
  (∀ k, w.idx k < 2 ^ DEPTH) ∧
  -- R2
  x.nf1 = nf x.d (w.sk 0) (w.leaf 0) (w.idx 0) ∧
  x.nf2 = nf x.d (w.sk 1) (w.leaf 1) (w.idx 1) ∧
  -- R3
  (∀ k, w.v k ≠ 0 → MR (w.leaf k) (w.idx k) (w.sib k) = x.root) ∧
  -- R4
  x.o1 = cm (w.oi 0) (w.ov 0) ∧ x.o2 = cm (w.oi 1) (w.ov 1) ∧
  -- R5
  (∀ y ∈ [w.v 0, w.v 1, w.ov 0, w.ov 1, x.pub, x.fee], y.val < 2 ^ 128) ∧
  (w.v 0).val + (w.v 1).val = (w.ov 0).val + (w.ov 1).val + x.pub.val + x.fee.val ∧
  -- R6
  0 < (w.v 0).val + (w.v 1).val ∧
  -- R7
  (∀ k : Fin 2, (w.ov k = 0 → w.oi k = ((k.val + 1 : ℕ) : F)) ∧
                (w.ov k ≠ 0 → w.oi k ≠ 1 ∧ w.oi k ≠ 2)) ∧
  -- R8
  x.nf1 ≠ x.nf2 ∧ x.o1 ≠ x.o2 ∧
  -- R9
  x.rcp.val < 2 ^ 160 ∧ 0 < x.auth.val ∧ x.auth.val < 2 ^ 160 ∧ (x.pub = 0 ↔ x.rcp = 0)

end MSP
