import Spec.System

/-!
# C2, C2c, C7, C8, C10 and the refinement: the deployed code

Step 5 defines every declaration below from one EVM semantics (EVMYulLean
extended with EIP-8141 frames, EIP-8250 keyed nonces and EIP-8272 recent roots,
P10) applied to the pinned bytecode, under the pinned gas schedule (P8). That
binding is reviewed like this file: choosing, say, `approvalsIn` or `Obs`'s
readers freely would make these claims trivial.
-/

namespace MSP

noncomputable section

open Classical

opaque ChainStateImpl : NonemptyType.{0}
/-- P10. A chain state, including the history the readers below need. -/
def ChainState : Type := ChainStateImpl.type
instance : Nonempty ChainState := ChainStateImpl.property
instance : Inhabited ChainState := Classical.inhabited_of_nonempty inferInstance

opaque DeploymentImpl : NonemptyType.{0}
/-- D12. A deployed pool. -/
def Deployment : Type := DeploymentImpl.type
instance : Nonempty Deployment := DeploymentImpl.property

/-- P9. The deployment matches D12 and the committed artifacts. -/
opaque Honest : Deployment → Prop
opaque addrOf : Deployment → ℕ
opaque chainOf : Deployment → ℕ
/-- The linked verifier's return value is 1 for these proof words and public signals. -/
opaque verifierOf : Deployment → List UInt8 → F × F × F → Prop

def poolOf (d : Deployment) (ext : List UInt8 → F × F × F → Assignment) : Pool :=
  ⟨addrOf d, chainOf d, verifierOf d, ext⟩

opaque chainInit : Deployment → ChainState
/-- One step: a transaction, or the next slot. -/
opaque ChainStep : Deployment → ChainState → ChainState → Prop

/-! Readers of a chain state -/

opaque balanceOf : ChainState → ℕ → ℕ
opaque storageAt : ChainState → ℕ → ℕ → ℕ
/-- EIP-8250: the current sequence of `(sender, key)`. -/
opaque nonceSeqOf : ChainState → ℕ → ℕ → ℕ
/-- EIP-8272: the root the canonical frame would accept for `(source, slot)` now. -/
opaque recentRootOf : ChainState → ℕ → ℕ → Option F
/-- The `cm` of every `LeafAppended` log address `a` emitted for epoch `e`, in order. -/
opaque leafLogs : ChainState → ℕ → ℕ → List F
/-- All ETH address `a` ever sent to `r`, other than gas payments. -/
opaque sentTo : ChainState → ℕ → ℕ → ℕ
opaque slotOf : ChainState → ℕ

/-- The model state `s` is what the chain state shows, up to ghost fields. -/
def Obs (d : Deployment) (st : ChainState) (s : PoolState) : Prop :=
  let A := addrOf d
  balanceOf st A = s.balance ∧
  (∀ r < 2 ^ 160, storageAt st A (K (u256 r ++ u256 23)) = s.credit r) ∧
  (∀ r, 2 ^ 160 ≤ r → s.credit r = 0) ∧
  (∀ k < 2 ^ 256, nonceSeqOf st A k ≠ 0 ↔ k ∈ s.keys) ∧
  storageAt st A 24 = s.E ∧ storageAt st A 21 = (s.leaves s.E).length ∧
  storageAt st A 22 = (TR (s.leaves s.E)).val ∧
  (∀ e < s.E, storageAt st A (K (u256 e ++ u256 25)) = (s.finalRoot e).val) ∧
  (∀ e, leafLogs st A e = s.leaves e) ∧
  (∀ src sl r, recentRootOf st src sl = some r → (src, sl, r) ∈ s.roots) ∧
  (∀ r, sentTo st A r = s.paid r) ∧
  slotOf st = s.slot

/-- The model events a chain step denotes, given P3's extractor: its
transaction's successful calls into the pool, decoded. -/
opaque eventsOf : Deployment → (List UInt8 → F × F × F → Assignment) →
  ChainState → ChainState → List Event
/-- Whether any code ran at the pool's address during the step. -/
opaque poolCodeRan : Deployment → ChainState → ChainState → Prop

inductive ChainRun (d : Deployment) : List ChainState → Prop
  | init : ChainRun d [chainInit d]
  | step {h st st'} : ChainRun d (h ++ [st]) → ChainStep d st st' → ChainRun d (h ++ [st, st'])

def eventsAlong (d : Deployment) (ext : List UInt8 → F × F × F → Assignment) :
    List ChainState → List Event
  | st :: st' :: rest => eventsOf d ext st st' ++ eventsAlong d ext (st' :: rest)
  | _ => []

def ReachableChain (d : Deployment) (st : ChainState) : Prop := ∃ h, ChainRun d (h ++ [st])

/-- Refinement, which also gives C5f: along every chain run, the events its
steps denote form a run of the model whose state the chain shows, ETH arrives
as `receive` only in steps where no pool code ran, or the run has a bad event.
It holds for every extractor, so no proof chooses the ghost witnesses. -/
def Refines : Prop :=
  ∀ d ext, Honest d → IdealVerifier (poolOf d ext) →
    ∀ h, ChainRun d h →
      ∃ s, Run (poolOf d ext) (eventsAlong d ext h) s ∧
        (BadEvent (poolOf d ext) (eventsAlong d ext h) s ∨ Obs d (h.getLast?.getD default) s) ∧
        ∀ i st st', h[i]? = some st → h[i + 1]? = some st' →
          (∃ v, Event.receive v ∈ eventsOf d ext st st') → ¬ poolCodeRan d st st'

/-- P5 to P7: `tx` is valid in `st`. -/
opaque ValidTx : ChainState → FrameTx → Prop
/-- Every `APPROVE` executed while `tx` runs from `st` by code whose `ADDRESS` is
the pool's, in any frame: its frame index and scope. -/
opaque approvalsIn : Deployment → ChainState → FrameTx → List (ℕ × ℕ)

/-- C2. The pool's code approves only in frame 1 of its own transactions, with
scope 3, and only what `Acc` describes. -/
def C2 : Prop :=
  ∀ d st tx, Honest d → ReachableChain d st → ValidTx st tx →
    ∀ ap ∈ approvalsIn d st tx,
      ap = (1, 3) ∧ tx.sender = addrOf d ∧ Acc (addrOf d) (chainOf d) (verifierOf d) 1 tx

/-- C2c. Given enough validation gas and balance, the pool approves every valid
transaction `Acc` describes. 216,141 is frame 1's measured minimum under `G`
(each nested call keeps back 1/64 of its gas); 195,840 is EIP-8250's first-use
state gas for two keys. -/
def C2c : Prop :=
  ∀ d st tx, Honest d → ReachableChain d st → ValidTx st tx →
    Acc (addrOf d) (chainOf d) (verifierOf d) 1 tx →
    216141 ≤ (tx.frames.getD 1 default).execLimit →
    195840 ≤ (tx.frames.getD 1 default).stateLimit →
    tx.maxCost ≤ balanceOf st (addrOf d) →
    (1, 3) ∈ approvalsIn d st tx

inductive Outcome | ok | reverted | outOfGas
deriving DecidableEq, Inhabited

/-- How frame 2 of `tx` ends, with its pinned limits, after frame 1 approved. -/
opaque frame2Outcome : Deployment → ChainState → FrameTx → Outcome

/-- C7. Settlement never runs out of gas, in any reachable state. -/
def C7 : Prop :=
  ∀ d st tx, Honest d → ReachableChain d st → ValidTx st tx → (1, 3) ∈ approvalsIn d st tx →
    frame2Outcome d st tx ≠ .outOfGas

/-- `hash2` and `hash3` of the linked libraries: the returned word and the gas used. -/
opaque libHash2 : Deployment → F → F → Option (ℕ × ℕ)
opaque libHash3 : Deployment → F → F → F → Option (ℕ × ℕ)

/-- C8. The libraries return `H2` and `H3` within 200,000 gas. -/
def C8 : Prop :=
  ∀ d, Honest d →
    (∀ a b, ∃ g, libHash2 d a b = some ((H2 a b).val, g) ∧ g ≤ 200000) ∧
    (∀ a b c, ∃ g, libHash3 d a b c = some ((H3 a b c).val, g) ∧ g ≤ 200000)

/-- Calling the pool from `caller` with `value` and calldata, with ample gas. -/
opaque callPool : Deployment → ChainState → ℕ → ℕ → List UInt8 → Outcome
/-- `r` accepts a plain ETH call with the gas a claim forwards. -/
opaque acceptsPlainETH : ChainState → ℕ → Prop

def publishCalldata (e : ℕ) : List UInt8 := [0xd0, 0x38, 0x70, 0xb3] ++ u256 e
def claimCalldata (r : ℕ) : List UInt8 := [0xa3, 0x06, 0x6a, 0xab] ++ u256 r

/-- C10. Anyone can publish an existing epoch's root and pay out a credit. -/
def C10 : Prop :=
  ∀ d st s caller, Honest d → ReachableChain d st → Obs d st s →
    (∀ e ≤ s.E, (if e = s.E then TR (s.leaves s.E) else s.finalRoot e) ≠ 0 →
      callPool d st caller 0 (publishCalldata e) = .ok) ∧
    (∀ r < 2 ^ 160, 0 < s.credit r → acceptsPlainETH st r →
      callPool d st caller 0 (claimCalldata r) = .ok)

end

end MSP
