import Spec.Circuit
import Spec.FrameTx
import Spec.Tree
import Mathlib.Data.Finsupp.Basic

/-!
# D13, C3 to C5: the pool as a state machine

The model is what the chain does to the pool's state, by P5 to P7 and the
logic's code. `Refines` in `Spec.Evm` ties it to the deployed bytecode.
-/

namespace MSP

noncomputable section

open Classical

/-- A deployment's fixed parameters, and P3's extractor. `verifies π pub` is the
linked verifier's return value for proof words `π` and public signals `pub`
(A6). `ext` maps a proof to an assignment. Every claim holds for every
extractor, so no proof can choose a convenient one; an approved spend whose
extraction fails is a bad event. -/
structure Pool where
  A : ℕ
  c : ℕ
  verifies : List UInt8 → F × F × F → Prop
  ext : List UInt8 → F × F × F → Assignment

instance : Inhabited Pool := ⟨⟨0, 0, fun _ _ => False, fun _ _ => default⟩⟩

/-- An idealized verifier, used only by the non-vacuity witness `W1`: the
extractor turns every accepted proof into a satisfying assignment with the same
public signals. A real Groth16 verifier accepts some proof for every public
input, so the claims never assume this; they count a failed extraction among
the run's spends as a bad event instead. -/
def IdealVerifier (P : Pool) : Prop :=
  ∀ π pub, P.verifies π pub → Satisfied (P.ext π pub) ∧ publicOf (P.ext π pub) = pub

/-- D14. -/
structure Occ where
  e : ℕ
  i : ℕ
deriving DecidableEq

/-- D13. Ghost fields are not on chain: they record openings, consumed
occurrences and cumulative credits and payouts, so that claims can name them. -/
structure PoolState where
  leaves : ℕ → List F
  /-- ghost: each leaf's value, from its opening -/
  vals : ℕ → List ℕ
  E : ℕ
  finalRoot : ℕ → F
  credit : ℕ →₀ ℕ
  balance : ℕ
  /-- every EIP-8272 write `(source_id, slot, root word)`, by the pool or anyone else -/
  roots : List (ℕ × ℕ × ℕ)
  /-- EIP-8250 keys consumed for sender `A` -/
  keys : List ℕ
  /-- ghost: occurrences consumed as nonzero-value inputs -/
  spent : List Occ
  /-- ghost: total ever credited to, and paid out to, each recipient -/
  credited : ℕ →₀ ℕ
  paid : ℕ →₀ ℕ
  slot : ℕ

def PoolState.init : PoolState :=
  ⟨fun _ => [], fun _ => [], 0, fun _ => 0, 0, 0, [], [], [], 0, 0, 0⟩

instance : Inhabited PoolState := ⟨PoolState.init⟩

/-- `_ensureCapacity(n)` rolls the epoch over. -/
def rollsOver (s : PoolState) (n : ℕ) : Prop := CAPACITY - (s.leaves s.E).length < n

/-- `_ensureCapacity` then `_insert`: a new epoch starts first when the new
leaves do not fit. -/
def PoolState.append (s : PoolState) (new : List (F × ℕ)) : PoolState :=
  let s := if rollsOver s new.length then
      { s with finalRoot := Function.update s.finalRoot s.E (TR (s.leaves s.E)), E := s.E + 1 }
    else s
  { s with leaves := Function.update s.leaves s.E (s.leaves s.E ++ new.map Prod.fst),
           vals := Function.update s.vals s.E (s.vals s.E ++ new.map Prod.snd) }

/-- Frame 2's settlement data. -/
def settleData (tx : FrameTx) : SettleData := SettleData.decode (tx.frames.getD 2 default).data

/-- Frame 1's proof words. -/
def proofOf (tx : FrameTx) : List UInt8 := (tx.frames.getD 1 default).data.take 256

/-- The public signals the dispatcher passed to the verifier (A6). -/
def verifiedPublics (tx : FrameTx) : F × F × F :=
  let x := (settleData tx).stmt
  let b : F := (wordAt (tx.frames.getD 1 default).data 256 : F)
  (b, γ x (α x + b), α x)

/-- The assignment P3's extractor gives for an approved transaction. -/
def extOf (P : Pool) (tx : FrameTx) : Assignment := P.ext (proofOf tx) (verifiedPublics tx)

/-- The number of non-sink outputs a settlement inserts. -/
def newCount (sd : SettleData) : ℕ :=
  (if sd.o1 = (SINK 0).val then 0 else 1) + (if sd.o2 = (SINK 1).val then 0 else 1)

/-- Every revert condition of `settle`: its checks, the ABI decoder's range
checks, and checked arithmetic on the epoch counter and the credit. -/
def SettlePre (s : PoolState) (P : Pool) (sd : SettleData) : Prop :=
  sd.epoch < 2 ^ 64 ∧ sd.rcp < 2 ^ 160 ∧ sd.auth < 2 ^ 160 ∧
  sd.nf1 ≠ 0 ∧ sd.nf2 ≠ 0 ∧ sd.auth ≠ 0 ∧ sd.domain = (D P.c P.A sd.epoch).val ∧ sd.epoch ≤ s.E ∧
  sd.root < p ∧ sd.domain < p ∧ sd.nf1 < p ∧ sd.nf2 < p ∧ sd.o1 < p ∧ sd.o2 < p ∧
  sd.pub < 2 ^ 128 ∧ sd.fee < 2 ^ 128 ∧ (sd.pub = 0 ↔ sd.rcp = 0) ∧
  sd.o1 ≠ sd.o2 ∧ sd.o1 ≠ (SINK 1).val ∧ sd.o2 ≠ (SINK 0).val ∧
  (rollsOver s (newCount sd) → s.E + 1 < 2 ^ 64) ∧
  (sd.pub ≠ 0 → s.credit sd.rcp + sd.pub < 2 ^ 256)

/-- The latest EIP-8272 write for `(source, slot)`, which replaced any earlier one. -/
def lastWrite (roots : List (ℕ × ℕ × ℕ)) (src sl : ℕ) : Option ℕ :=
  ((roots.filter fun w => w.1 = src ∧ w.2.1 = sl).getLast?).map fun w => w.2.2

/-- The non-sink outputs a settlement inserts, with their values from the witness. -/
def newLeaves (sd : SettleData) (w : Witness) : List (F × ℕ) :=
  (if sd.o1 = (SINK 0).val then [] else [((sd.o1 : F), (w.ov 0).val)]) ++
  (if sd.o2 = (SINK 1).val then [] else [((sd.o2 : F), (w.ov 1).val)])

/-- The occurrences a spend consumes: its nonzero-value inputs. -/
def inputsOf (sd : SettleData) (w : Witness) : List Occ :=
  ((List.finRange 2).filter fun k => w.v k ≠ 0).map fun k => ⟨sd.epoch, w.idx k⟩

/-- Calls into the pool that return successfully and whose effects persist,
whether or not they change state, and the other chain actions the pool observes.
A reverted call has no event. -/
inductive Event
  /-- `shield(inner)` with `msg.value = v` -/
  | shield (inner : F) (v : ℕ)
  /-- `publishEpochRoot(e)` -/
  | publish (e : ℕ)
  /-- an EIP-8272 write by another address `a` with salt `salt` and root word `root` -/
  | rootWrite (a salt root : ℕ)
  /-- `claimWithdrawal(r)`, paying `r` -/
  | claim (r : ℕ)
  /-- ETH reaching the pool other than by a call to it, or held at deployment -/
  | receive (v : ℕ)
  /-- a frame transaction whose frame 1 the pool approved, and the gas the pool paid -/
  | spend (tx : FrameTx) (gasPaid : ℕ)
  /-- the next slot -/
  | tick

/-- One transition. A spend's settlement succeeds exactly when `SettlePre`
holds; refinement requires the chain to agree, gas included (C7). -/
def Step (P : Pool) (s : PoolState) : Event → PoolState → Prop
  | .shield inr v, s' =>
      0 < v ∧ v < 2 ^ 128 ∧ cm inr v ≠ SINK 0 ∧ cm inr v ≠ SINK 1 ∧
      (rollsOver s 1 → s.E + 1 < 2 ^ 64) ∧
      s' = { s.append [(cm inr v, v)] with balance := s.balance + v }
  | .publish e, s' =>
      e < 2 ^ 64 ∧ e ≤ s.E ∧
      (let r := if e = s.E then TR (s.leaves s.E) else s.finalRoot e
       r ≠ 0 ∧ s' = { s with roots := s.roots ++ [(sourceId P.A e, s.slot, r.val)] })
  | .rootWrite a salt r, s' =>
      addr20 a ≠ addr20 P.A ∧ r < 2 ^ 256 ∧ s' = { s with roots := s.roots ++ [(K (addr20 a ++ u256 salt), s.slot, r)] }
  | .claim r, s' =>
      0 < s.credit r ∧ s.credit r ≤ s.balance ∧
      s' = { s with balance := s.balance - s.credit r, credit := s.credit.erase r,
                    paid := s.paid + Finsupp.single r (s.credit r) }
  | .receive v, s' => s' = { s with balance := s.balance + v }
  | .tick, s' => s' = { s with slot := s.slot + 1 }
  | .spend tx gas, s' =>
      let sd := settleData tx
      let w := witOf (extOf P tx)
      -- the pool approved (C2)
      Acc P.A P.c P.verifies 1 tx ∧
      -- P6: keys are words, strictly increasing and unused
      (∀ k ∈ tx.nonceKeys, k < 2 ^ 256) ∧ tx.nonceKeys.Pairwise (· < ·) ∧
      (∀ k ∈ tx.nonceKeys, k ∉ s.keys) ∧
      -- P7: frame 0 names the latest write for its source and slot, in the usable window
      (lastWrite s.roots (sourceId P.A sd.epoch) sd.rootSlot = some sd.root ∧
        sd.rootSlot < s.slot ∧ s.slot ≤ sd.rootSlot + 8191) ∧
      -- P5: the pool can pay the maximum cost and pays at most that
      tx.maxCost ≤ s.balance ∧ gas ≤ tx.maxCost ∧
      let s1 := { s with keys := s.keys ++ tx.nonceKeys, spent := s.spent ++ inputsOf sd w,
                         balance := s.balance - gas }
      s' = if SettlePre s P sd then
             let s2 := s1.append (newLeaves sd w)
             if sd.pub = 0 then s2
             else { s2 with credit := s2.credit + Finsupp.single sd.rcp sd.pub,
                            credited := s2.credited + Finsupp.single sd.rcp sd.pub }
           else s1

/-- Runs from deployment. -/
inductive Run (P : Pool) : List Event → PoolState → Prop
  | nil : Run P [] PoolState.init
  | snoc {evs s e s'} : Run P evs s → Step P s e s' → Run P (evs ++ [e]) s'

/-! ## Bad events, relative to what the execution hashed -/

inductive Query
  | h2 (a b : F)
  | h3 (a b c : F)
  | keccak (m : List UInt8)
  | dom (c a e : ℕ)

/-- Two queries of one kind with different inputs and equal outputs. -/
def Query.collide : Query → Query → Prop
  | .h2 a b, .h2 a' b' => (a, b) ≠ (a', b') ∧ H2 a b = H2 a' b'
  | .h3 a b c, .h3 a' b' c' => (a, b, c) ≠ (a', b', c') ∧ H3 a b c = H3 a' b' c'
  | .keccak m, .keccak m' => m ≠ m' ∧ K m = K m'
  | .dom c a e, .dom c' a' e' => (c, a, e) ≠ (c', a', e') ∧ D c a e = D c' a' e'
  | _, _ => False

/-- A query whose output is structurally special: a Poseidon output of 0, the
empty leaf and empty storage, or a Keccak output below `2 ^ 64`, where fixed
storage slots and empty storage live. -/
def Query.degenerate : Query → Prop
  | .h2 a b => H2 a b = 0
  | .h3 a b c => H3 a b c = 0
  | .keccak m => K m < 2 ^ 64
  | _ => False

/-- The `H2` inputs along a path. -/
def pathQueries (leaf : F) (i : ℕ) (sib : Fin DEPTH → F) : List Query :=
  ((List.finRange DEPTH).foldl
    (fun (acc : F × List Query) l =>
      if i.testBit l.val then (H2 (sib l) acc.1, acc.2 ++ [Query.h2 (sib l) acc.1])
      else (H2 acc.1 (sib l), acc.2 ++ [Query.h2 acc.1 (sib l)]))
    (leaf, [])).2

/-- Every hash a valid-spend check evaluates for `x` and `w`. -/
def witnessQueries (x : Statement) (w : Witness) : List Query :=
  ((List.finRange 2).flatMap fun k =>
    [Query.h3 1 (w.sk k) 0, .h2 (pk (w.sk k)) (w.ρ k), .h3 2 (inner (w.sk k) (w.ρ k)) (w.v k),
     .h2 x.d (w.sk k), .h2 (w.leaf k) (w.idx k : F),
     .h3 4 (nfKey x.d (w.sk k)) (H2 (w.leaf k) (w.idx k : F))] ++
    pathQueries (w.leaf k) (w.idx k) (w.sib k)) ++
  [.h3 2 (w.oi 0) (w.ov 0), .h3 2 (w.oi 1) (w.ov 1)]

/-- Every node pair `TR` evaluates. -/
def treeQueries : ℕ → List F → List Query
  | 0, _ => []
  | h + 1, L =>
      treeQueries h (L.take (2 ^ h)) ++ treeQueries h (L.drop (2 ^ h)) ++
      [.h2 (treeRoot h (L.take (2 ^ h))) (treeRoot h (L.drop (2 ^ h)))]

def eventQueries (P : Pool) : Event → List Query
  | .shield inr v => [.h3 2 inr v]
  | .rootWrite a salt _ => [.keccak (addr20 a ++ u256 salt)]
  | .spend tx _ =>
      let sd := settleData tx
      witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)) ++
      [.dom P.c P.A sd.epoch, .keccak (addr20 P.A ++ u256 sd.epoch),
       .keccak (u256 tx.nonceKeys.length ++ tx.nonceKeys.flatMap u256),
       .keccak (u256 2 ++ u256 (min sd.nf1 sd.nf2) ++ u256 (max sd.nf1 sd.nf2)),
       .keccak (rrEntryMsg (sourceId P.A sd.epoch) sd.rootSlot sd.root),
       .keccak (rrKeyMsg (sourceId P.A sd.epoch) (sd.rootSlot % 8192))] ++
      (if sd.pub = 0 then [] else [.keccak (creditMsg sd.rcp)])
  | .claim r => [.keccak (creditMsg r)]
  | _ => []

/-- What a run hashed: the sinks the code hardcodes, each event's queries,
every tree root of every prefix of every epoch, each epoch's domain and root
source, each closed epoch's storage slot, and the entry and storage key of every
EIP-8272 write. -/
def traceQueries (P : Pool) (evs : List Event) (s : PoolState) : List Query :=
  [Query.h3 2 1 0, .h3 2 2 0] ++
  evs.flatMap (eventQueries P) ++
  s.roots.flatMap (fun w => [Query.keccak (rrEntryMsg w.1 w.2.1 w.2.2),
                             .keccak (rrKeyMsg w.1 (w.2.1 % 8192))]) ++
  (List.range s.E).map (fun e => Query.keccak (finalRootMsg e)) ++
  (List.range (s.E + 1)).flatMap fun e =>
    [Query.dom P.c P.A e, .keccak (addr20 P.A ++ u256 e)] ++
    (List.range ((s.leaves e).length + 1)).flatMap fun n => treeQueries DEPTH ((s.leaves e).take n)

/-- A compression break (P4): an approved spend whose extracted assignment
proves another statement. -/
def CompressionBreak (P : Pool) (evs : List Event) : Prop :=
  ∃ tx g, Event.spend tx g ∈ evs ∧ stmtOf (extOf P tx) ≠ (settleData tx).stmt

/-- An extraction failure (P3): an approved spend whose proof the extractor does
not turn into a satisfying assignment with the verified public signals. -/
def ExtractionFailure (P : Pool) (evs : List Event) : Prop :=
  ∃ tx g, Event.spend tx g ∈ evs ∧
    ¬ (Satisfied (extOf P tx) ∧ publicOf (extOf P tx) = verifiedPublics tx)

/-- A bad event among the run's own queries, plus `extra` ones a claim names. -/
def BadEventWith (P : Pool) (evs : List Event) (s : PoolState) (extra : List Query) : Prop :=
  (∃ q₁ ∈ traceQueries P evs s ++ extra, ∃ q₂ ∈ traceQueries P evs s ++ extra, q₁.collide q₂) ∨
  (∃ q ∈ traceQueries P evs s ++ extra, q.degenerate) ∨
  CompressionBreak P evs ∨ ExtractionFailure P evs

def BadEvent (P : Pool) (evs : List Event) (s : PoolState) : Prop := BadEventWith P evs s []

/-- The hash inputs of an opening of occurrence `(e, i)` with key `sk`. -/
def openingQueries (P : Pool) (e i : ℕ) (sk ρ v : F) : List Query :=
  [.h3 1 sk 0, .h2 (pk sk) ρ, .h3 2 (inner sk ρ) v, .h2 (D P.c P.A e) sk,
   .h2 (cm (inner sk ρ) v) (i : F),
   .h3 4 (nfKey (D P.c P.A e) sk) (H2 (cm (inner sk ρ) v) (i : F)), .dom P.c P.A e]

/-! ## Claims over the model -/

/-- The statement a spend's settlement carries. -/
abbrev stmtOfTx (tx : FrameTx) : Statement := (settleData tx).stmt

/-- C3. An approved spend proves a valid spend of its own settlement statement,
consumes exactly its two nullifiers, names a root the pool wrote, and is
signed by `auth` over the canonical hash. -/
def C3 (P : Pool) : Prop :=
  ∀ evs s tx g s', Run P evs s → Step P s (.spend tx g) s' →
    BadEvent P (evs ++ [.spend tx g]) s' ∨
    (R (stmtOfTx tx) (witOf (extOf P tx)) ∧
     tx.nonceKeys = [min (settleData tx).nf1 (settleData tx).nf2,
                     max (settleData tx).nf1 (settleData tx).nf2] ∧
     (∃ n ≤ (s.leaves (settleData tx).epoch).length,
        ((settleData tx).root : F) = TR ((s.leaves (settleData tx).epoch).take n)) ∧
     SignsCanonicalHash tx (settleData tx).auth)

/-- P13's bound: the epoch counter can still roll over, and the balance is a word. -/
def Bounded (s : PoolState) : Prop := s.E + 1 < 2 ^ 64 ∧ s.balance < 2 ^ 256

/-- C4 over the model: an approved spend's settlement passes every check. -/
def C4 (P : Pool) : Prop :=
  ∀ evs s tx g s', Run P evs s → Step P s (.spend tx g) s' →
    BadEvent P (evs ++ [.spend tx g]) s' ∨ ¬ Bounded s ∨ SettlePre s P (settleData tx)

/-- C5a. Every leaf opens to a positive value below `2 ^ 128` and is no sink. -/
def C5a (P : Pool) : Prop :=
  ∀ evs s, Run P evs s → BadEvent P evs s ∨
    ∀ e i, i < (s.leaves e).length →
      (s.vals e).length = (s.leaves e).length ∧
      0 < (s.vals e).getD i 0 ∧ (s.vals e).getD i 0 < 2 ^ 128 ∧
      (s.leaves e).getD i 0 ≠ SINK 0 ∧ (s.leaves e).getD i 0 ≠ SINK 1 ∧
      ∃ inr, (s.leaves e).getD i 0 = cm inr ((s.vals e).getD i 0 : F)

/-- C5b. Each nonzero-value input of an approved spend is an existing, unspent
occurrence of the spend's epoch, holding the witness's leaf and value, and a
spend's two inputs differ. -/
def C5b (P : Pool) : Prop :=
  ∀ evs s tx g s', Run P evs s → Step P s (.spend tx g) s' →
    BadEvent P (evs ++ [.spend tx g]) s' ∨
    let w := witOf (extOf P tx)
    let e := (settleData tx).epoch
    (∀ k, w.v k ≠ 0 →
      w.idx k < (s.leaves e).length ∧ (s.leaves e).getD (w.idx k) 0 = w.leaf k ∧
      (s.vals e).getD (w.idx k) 0 = (w.v k).val ∧ (⟨e, w.idx k⟩ : Occ) ∉ s.spent) ∧
    (w.v 0 ≠ 0 → w.v 1 ≠ 0 → w.idx 0 ≠ w.idx 1)

/-- The value the pool owes: unspent occurrences and credits. -/
def owed (s : PoolState) : ℕ :=
  (∑ e ∈ Finset.range (s.E + 1), ∑ i ∈ Finset.range (s.vals e).length,
      if (⟨e, i⟩ : Occ) ∈ s.spent then 0 else (s.vals e).getD i 0) +
  s.credit.sum fun _ v => v

/-- C5c. The pool holds at least what it owes. -/
def C5c (P : Pool) : Prop :=
  ∀ evs s, Run P evs s → BadEvent P evs s ∨ owed s ≤ s.balance

/-- C5d. Each recipient's credit is what it was credited minus what it was paid. -/
def C5d (P : Pool) : Prop :=
  ∀ evs s, Run P evs s → ∀ r, s.credit r + s.paid r = s.credited r

/-- C5e. Every root written under the source of an epoch `e < 2 ^ 64` is the tree
root of a prefix of that epoch, which exists. The bad event may use that
source's Keccak input. -/
def C5e (P : Pool) : Prop :=
  ∀ evs s, Run P evs s →
    ∀ r ∈ s.roots, ∀ e < 2 ^ 64, r.1 = sourceId P.A e →
      BadEventWith P evs s [.keccak (addr20 P.A ++ u256 e)] ∨
      (e ≤ s.E ∧ ∃ n ≤ (s.leaves e).length, r.2.2 = (TR ((s.leaves e).take n)).val)

/-- C5g. A consumed key that is some occurrence's nullifier, under any opening
of its leaf, consumes that occurrence as an input of this spend. -/
def C5g (P : Pool) : Prop :=
  ∀ evs s tx g s', Run P evs s → Step P s (.spend tx g) s' →
    ∀ (o : Occ) (sk ρ v : F), o.i < (s.leaves o.e).length →
      (s.leaves o.e).getD o.i 0 = cm (inner sk ρ) v →
      (nf (D P.c P.A o.e) sk ((s.leaves o.e).getD o.i 0) o.i).val ∈ tx.nonceKeys →
      BadEventWith P (evs ++ [.spend tx g]) s' (openingQueries P o.e o.i sk ρ v) ∨
      o ∈ inputsOf (settleData tx) (witOf (extOf P tx))

/-- C5h. An unspent occurrence's nullifier, under any opening, is unconsumed. -/
def C5h (P : Pool) : Prop :=
  ∀ evs s, Run P evs s →
    ∀ (o : Occ) (sk ρ v : F), o.i < (s.leaves o.e).length → o ∉ s.spent →
      (s.leaves o.e).getD o.i 0 = cm (inner sk ρ) v →
      BadEventWith P evs s (openingQueries P o.e o.i sk ρ v) ∨
      (nf (D P.c P.A o.e) sk ((s.leaves o.e).getD o.i 0) o.i).val ∉ s.keys

/-- The siblings of leaf `i` in the complete tree over `L`: at level `l`, the
root of the neighboring subtree of height `l`. -/
def siblingsOf (L : List F) (i : ℕ) : Fin DEPTH → F := fun l =>
  treeRoot l.val ((L.drop (((i / 2 ^ l.val) ^^^ 1) * 2 ^ l.val)).take (2 ^ l.val))

/-- The canonical spend of occurrence `i` of epoch `e`, whose tree is `L`, with
opening `(sk, ρ, v)`, a dummy second input `(skd, ρd)`, fee `f`, recipient
`rcp` and authorizer `auth`: both outputs are sinks and `v - f` is withdrawn. -/
def mkSpend (P : Pool) (e : ℕ) (L : List F) (i : ℕ) (sk ρ v skd ρd f rcp auth : F) :
    Statement × Witness :=
  let d := D P.c P.A e
  let w : Witness := ⟨![sk, skd], ![ρ, ρd], ![v, 0], ![i, 0], ![siblingsOf L i, fun _ => 0],
                      ![1, 2], ![0, 0]⟩
  (⟨nf d sk (w.leaf 0) i, nf d skd (w.leaf 1) 0, SINK 0, SINK 1, TR L, d, v - f, f, rcp, auth⟩, w)

/-- Spendability. Whoever holds an opening of an unspent occurrence can spend it
against any root of its epoch that contains it, for every choice of dummy input,
fee below the value, recipient and authorizer, as long as the dummy is fresh:
the canonical spend is valid and its keys are nonzero and unconsumed. Quantifying over the dummy, rather than asking for
one, keeps a proof from choosing a dummy whose hashes collide. With C1c and C2c
the spend is then approved. -/
def Spendable (P : Pool) : Prop :=
  ∀ evs s, Run P evs s →
    ∀ (o : Occ) (sk ρ : F), o.i < (s.leaves o.e).length → o ∉ s.spent →
      let v : F := ((s.vals o.e).getD o.i 0 : F)
      (s.leaves o.e).getD o.i 0 = cm (inner sk ρ) v →
      ∀ n, o.i < n → n ≤ (s.leaves o.e).length →
      ∀ (skd ρd f rcp auth : F), f.val < v.val → 0 < rcp.val → rcp.val < 2 ^ 160 →
        0 < auth.val → auth.val < 2 ^ 160 →
        -- a fresh dummy: its nullifier key was never hashed in this run
        Query.h2 (D P.c P.A o.e) skd ∉ traceQueries P evs s →
        let xw := mkSpend P o.e ((s.leaves o.e).take n) o.i sk ρ v skd ρd f rcp auth
        BadEventWith P evs s (openingQueries P o.e o.i sk ρ v ++ witnessQueries xw.1 xw.2) ∨
        (R xw.1 xw.2 ∧ xw.1.nf1 ≠ 0 ∧ xw.1.nf2 ≠ 0 ∧ xw.1.nf1.val ∉ s.keys ∧ xw.1.nf2.val ∉ s.keys)

end

end MSP
