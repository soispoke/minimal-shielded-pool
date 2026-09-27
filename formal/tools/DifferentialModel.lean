import Spec.System

/-!
# Differential-test driver: the executable model against `wallet/wallet.py`

`formal/tools/differential_model.py` appends generated `#eval` lines to a copy
of this file and runs it with `lake env lean`. Each case prints lines
`R <case> <field> <decimal>`, which the script compares with the wallet.
Evaluation results are tests, not kernel-checked theorems.

Most quantities are evaluated through the `Spec` definitions themselves. Only
`treeRoot` needs help: its compiled code recomputes every all-zero subtree, so
one `TR` costs about `2 ^ 21` Poseidon calls (about 15 minutes interpreted).
`treeRootFast` returns `Z h` for an empty list and is otherwise the same
recursion; `treeRootFast_eq` proves it equal to `treeRoot`, and the `…Fast`
copies of `TR`, `siblingsOf` and `mkSpend` are proved equal to the `Spec`
definitions below, so evaluating them evaluates the `Spec` values. This file
registers no `csimp` lemma, so a generated `#eval` of `treeRoot`, `TR`,
`siblingsOf` or `mkSpend` still runs the `Spec` code unchanged.
-/

namespace MSP.Differential

open MSP

/-! ## The fast tree root and its equivalence with `treeRoot` -/

theorem treeRoot_nil (h : ℕ) : treeRoot h [] = Z h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [treeRoot, List.take_nil, List.drop_nil, ih, Z]

def treeRootFast : ℕ → List F → F
  | h, [] => Z h
  | 0, a :: _ => a
  | h + 1, a :: t =>
      H2 (treeRootFast h ((a :: t).take (2 ^ h))) (treeRootFast h ((a :: t).drop (2 ^ h)))

theorem treeRootFast_eq (h : ℕ) (L : List F) : treeRootFast h L = treeRoot h L := by
  induction h generalizing L with
  | zero => cases L <;> rfl
  | succ h ih =>
      cases L with
      | nil => simp only [treeRootFast, treeRoot_nil]
      | cons a t => simp only [treeRootFast, treeRoot, ih]

/-! ## Copies of `TR`, `siblingsOf` and `mkSpend` over `treeRootFast` -/

def TRFast (L : List F) : F := treeRootFast DEPTH L

theorem TRFast_eq (L : List F) : TRFast L = TR L := treeRootFast_eq DEPTH L

def siblingsOfFast (L : List F) (i : ℕ) : Fin DEPTH → F := fun l =>
  treeRootFast l.val ((L.drop (((i / 2 ^ l.val) ^^^ 1) * 2 ^ l.val)).take (2 ^ l.val))

theorem siblingsOfFast_eq (L : List F) (i : ℕ) : siblingsOfFast L i = siblingsOf L i := by
  funext l
  simp only [siblingsOfFast, siblingsOf, treeRootFast_eq]

/-- `mkSpend` with the pool's chain id `c` and address `A` passed directly, since
`mkSpend` reads nothing else of the pool. -/
def mkSpendFast (c A e : ℕ) (L : List F) (i : ℕ) (sk ρ v skd ρd f rcp auth : F) :
    Statement × Witness :=
  let d := D c A e
  let w : Witness := ⟨![sk, skd], ![ρ, ρd], ![v, 0], ![i, 0], ![siblingsOfFast L i, fun _ => 0],
                      ![1, 2], ![0, 0]⟩
  (⟨nf d sk (w.leaf 0) i, nf d skd (w.leaf 1) 0, SINK 0, SINK 1, TRFast L, d, v - f, f, rcp, auth⟩, w)

theorem mkSpendFast_eq (P : Pool) (e : ℕ) (L : List F) (i : ℕ) (sk ρ v skd ρd f rcp auth : F) :
    mkSpendFast P.c P.A e L i sk ρ v skd ρd f rcp auth =
      mkSpend P e L i sk ρ v skd ρd f rcp auth := by
  simp only [mkSpendFast, mkSpend, TRFast_eq, siblingsOfFast_eq]

/-! ## Output -/

def out (cid field : String) (x : ℕ) : IO Unit := IO.println s!"R {cid} {field} {x}"
def outF (cid field : String) (x : F) : IO Unit := out cid field x.val

def fs (xs : List ℕ) : List F := xs.map (fun n => (n : F))

def stmtOfList (xs : List ℕ) : Statement :=
  let g := fun j => ((xs.getD j 0 : ℕ) : F)
  ⟨g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9⟩

def printStmt (cid : String) (x : Statement) (s : F) : IO Unit := do
  for j in List.finRange 10 do outF cid s!"x{j.val}" (x.vec j)
  outF cid "alpha" (α x)
  outF cid "beta" (β x)
  outF cid "gamma" (γ x s)

/-! ## Case evaluators -/

/-- D3 and D5 for one note: `pk`, `inner`, `cm`, `nfKey` and `nf`. -/
def noteCase (cid : String) (sk ρ v d i : ℕ) : IO Unit := do
  let leaf := cm (inner sk ρ) v
  outF cid "pk" (pk sk)
  outF cid "inner" (inner sk ρ)
  outF cid "cm" leaf
  outF cid "nfKey" (nfKey d sk)
  outF cid "nf" (nf d sk leaf i)

/-- D3's `cm` on an arbitrary inner value (the wallet's output commitment). -/
def cmCase (cid : String) (inr v : ℕ) : IO Unit := outF cid "cm" (cm inr v)

/-- D4. -/
def domainCase (cid : String) (c a e : ℕ) : IO Unit := outF cid "D" (D c a e)

/-- D4's tag, D6's sinks, D7's zero hashes and empty root, and C6's constants. -/
def constCase : IO Unit := do
  out "const" "DOMAIN_TAG" DOMAIN_TAG
  outF "const" "SINK0" (SINK 0)
  outF "const" "SINK1" (SINK 1)
  for l in List.range (DEPTH + 1) do outF "const" s!"Z{l}" (Z l)
  outF "const" "EMPTY_ROOT" EMPTY_ROOT
  for l in List.range DEPTH do outF "const" s!"zeroConst{l}" (zeroConst l)
  outF "const" "EMPTY_ROOT_CONST" (EMPTY_ROOT_CONST : F)

/-- `treeRoot h L` evaluated directly from `Spec`, for a small height. -/
def smallTreeCase (cid : String) (h : ℕ) (L : List ℕ) : IO Unit :=
  outF cid "treeRoot" (treeRoot h (fs L))

/-- D7 on a leaf list and an index: `TR`, `siblingsOf` (the first `direct`
levels also straight from `Spec`), the index bits, `MR` over the wallet's
siblings and over the model's, and C6's incremental `LogicTree` root. -/
def treeCase (cid : String) (L : List ℕ) (i : ℕ) (walletSibs : List ℕ) (direct : ℕ) :
    IO Unit := do
  let L := fs L
  outF cid "TR" (TRFast L)
  let sib := siblingsOfFast L i
  for l in List.finRange DEPTH do
    outF cid s!"sib{l.val}" (sib l)
    out cid s!"bit{l.val}" (if i.testBit l.val then 1 else 0)
    if l.val < direct then outF cid s!"sibDirect{l.val}" (siblingsOf L i l)
  outF cid "MRwallet" (MR (L.getD i 0) i (fun l => ((walletSibs.getD l.val 0 : ℕ) : F)))
  outF cid "MRmodel" (MR (L.getD i 0) i sib)
  outF cid "logicRoot" (L.foldl LogicTree.insert LogicTree.empty).root

/-- D9 on an arbitrary statement. -/
def compressionCase (cid : String) (xs : List ℕ) (s : ℕ) : IO Unit :=
  printStmt cid (stmtOfList xs) s

def printSpend (cid : String) (xw : Statement × Witness) (s : F) : IO Unit := do
  let (x, w) := xw
  printStmt cid x s
  for k in List.finRange 2 do
    outF cid s!"sk{k.val}" (w.sk k)
    outF cid s!"rho{k.val}" (w.ρ k)
    outF cid s!"v{k.val}" (w.v k)
    out cid s!"idx{k.val}" (w.idx k)
    outF cid s!"oi{k.val}" (w.oi k)
    outF cid s!"ov{k.val}" (w.ov k)
    outF cid s!"leaf{k.val}" (w.leaf k)
    for l in List.finRange DEPTH do
      outF cid s!"sib{k.val}_{l.val}" (w.sib k l)

/-- The canonical spend, through `mkSpendFast` (equal to `mkSpend` by `mkSpendFast_eq`). -/
def spendCase (cid : String) (c A e : ℕ) (L : List ℕ) (i sk ρ v skd ρd f rcp auth s : ℕ) :
    IO Unit :=
  printSpend cid (mkSpendFast c A e (fs L) i sk ρ v skd ρd f rcp auth) s

/-- A pool with chain id `c` and address `A`; `mkSpend` reads nothing else. -/
def poolWith (c A : ℕ) : Pool := ⟨A, c, fun _ _ => False, fun _ _ => fun _ => 0⟩

/-- The canonical spend through `Spec`'s `mkSpend` itself: slow (about
`3 * 2 ^ 20` Poseidon calls for `TR` and the siblings). -/
def spendDirectCase (cid : String) (c A e : ℕ) (L : List ℕ) (i sk ρ v skd ρd f rcp auth s : ℕ) :
    IO Unit :=
  printSpend cid (mkSpend (poolWith c A) e (fs L) i sk ρ v skd ρd f rcp auth) s

end MSP.Differential

open MSP.Differential

/-! Generated cases follow. -/
