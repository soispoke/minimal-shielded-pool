import Spec.System

/-!
# C2, C2c, C8, C10 and the refinement: the deployed code

Step 5 defines every opaque declaration below from one EVM semantics
(EVMYulLean extended with EIP-8141 frames, EIP-8250 keyed nonces and EIP-8272
recent roots, P10) applied to the pinned bytecode, under the pinned gas schedule
(P8). That binding is reviewed like this file: choosing, say, `ChainStep`,
`eventsOf` or `approvalsIn` freely would make these claims trivial. The parts of
a chain state the model observes are concrete fields, so no reader can be chosen.
-/

namespace MSP

noncomputable section

open Classical

opaque ChainRestImpl : NonemptyType.{0}
/-- The rest of a chain state: code, account nonces, other logs, history. -/
def ChainRest : Type := ChainRestImpl.type
instance : Nonempty ChainRest := ChainRestImpl.property

/-- P10. A chain state, with the history the model observes. -/
structure ChainState where
  balance : ℕ → ℕ
  storage : ℕ → ℕ → ℕ
  /-- the `cm` of every persisting `LeafAppended` log each address emitted for each epoch, in order -/
  leafLogs : ℕ → ℕ → List F
  /-- all ETH each address sent to each other address in transfers that persist, other than gas payments and refunds -/
  sentTo : ℕ → ℕ → ℕ
  /-- every persisting EIP-8272 write, in order: writer, salt, slot, root word -/
  rootWrites : List (ℕ × ℕ × ℕ × ℕ)
  slot : ℕ
  rest : ChainRest

instance : Nonempty ChainState :=
  ⟨⟨fun _ => 0, fun _ _ => 0, fun _ _ => [], fun _ _ => 0, [], 0, Classical.choice inferInstance⟩⟩
instance : Inhabited ChainState := Classical.inhabited_of_nonempty inferInstance

opaque DeploymentImpl : NonemptyType.{0}
/-- D12. A deployed pool. -/
def Deployment : Type := DeploymentImpl.type
instance : Nonempty Deployment := DeploymentImpl.property

/-- P9. The deployment matches D12 and the committed artifacts. -/
opaque Honest : Deployment → Prop
opaque addrOf : Deployment → ℕ
opaque chainOf : Deployment → ℕ
/-- The linked verifier returns 1 for these proof words and public signals when
its call frame starts with 500,000 gas (the dispatcher's gas operand; frame 1's
limit may leave less, which C2c covers). -/
opaque verifierOf : Deployment → List UInt8 → F × F × F → Prop
/-- EIP-8250's `NONCE_MANAGER`, chosen by the fork configuration. -/
opaque NONCE_MANAGER : ℕ

def poolOf (d : Deployment) (ext : List UInt8 → F × F × F → Assignment) : Pool :=
  ⟨addrOf d, chainOf d, verifierOf d, ext⟩

/-- The chain state right after the deployment transaction; its `slot` is that block's slot. -/
opaque chainInit : Deployment → ChainState
/-- One step: any transaction valid in `st` in the current open block, run with
`SLOTNUM = slot`; the end of that block, which applies its withdrawals and
end-of-block system calls; or the next slot, which advances `slot` by one and
is either empty or opens a block with any header the consensus rules allow
(number, timestamp, fee recipient, prevrandao, base fee, gas limit), with its
start-of-block system calls. -/
opaque ChainStep : Deployment → ChainState → ChainState → Prop

/-- The model state `s` is what the chain state shows, up to ghost fields. Every
clause about a hash-indexed storage slot names only keys the model holds, so no
collision with a key nobody hashed can falsify it. -/
def Obs (d : Deployment) (st : ChainState) (s : PoolState) : Prop :=
  let A := addrOf d
  st.balance A = s.balance ∧
  (∀ r, 0 < s.credit r → st.storage A (K (creditMsg r)) = s.credit r) ∧
  (∀ k ∈ s.keys, st.storage NONCE_MANAGER (K (u256 A ++ u256 k)) ≠ 0) ∧
  st.storage A 24 = s.E ∧ st.storage A 21 = (s.leaves s.E).length ∧
  st.storage A 22 = (TR (s.leaves s.E)).val ∧
  (∀ e < s.E, st.storage A (K (finalRootMsg e)) = (s.finalRoot e).val) ∧
  (∀ e, st.leafLogs A e = s.leaves e) ∧
  (∀ e ≤ s.E, ∀ sl r, lastWrite s.roots (sourceId A e) sl = some r →
    sl < s.slot → s.slot ≤ sl + 8191 →
    st.storage RECENT_ROOT (K (rrKeyMsg (sourceId A e) (sl % 8192))) =
      K (rrEntryMsg (sourceId A e) sl r)) ∧
  (∀ r, st.sentTo A r = s.paid r) ∧
  st.slot = s.slot

/-- The model events of a chain step, in execution order: each call into the
pool whose calldata begins with the selector of `shield`, `publishEpochRoot` or
`claimWithdrawal` and that returns successfully and whose effects persist,
whether or not it changes state, decoded from that call's own calldata and
`CALLVALUE` (a shield's `inner` is its calldata word and `v` its `CALLVALUE`).
A call into the pool is a `CALL` whose recipient is the pool or a non-VERIFY
frame whose target is the pool; not the pool's own `DELEGATECALL` into its
logic, and not another contract's `DELEGATECALL` or `CALLCODE` to the pool's
code. Then: each spend, a
transaction whose frame 1 the pool approved, with the gas the pool paid, placed
at its settlement, before the events of its later frames; each
EIP-8272 write by another address; `receive` for ETH credited to the pool other
than by a call to it or as a gas refund; and `tick` at a new slot. Any other
successful call must leave what `Obs` reads unchanged. -/
opaque eventsOf : Deployment → ChainState → ChainState → List Event

/-- ETH credited to the pool in a step other than by a call to it or a gas refund:
priority fees, `SELFDESTRUCT` beneficiaries, withdrawals. -/
opaque passiveInflow : Deployment → ChainState → ChainState → ℕ

def receivedIn (evs : List Event) : ℕ :=
  (evs.map fun | .receive v => v | _ => 0).sum

inductive ChainRun (d : Deployment) : List ChainState → Prop
  | init : ChainRun d [chainInit d]
  | step {h st st'} : ChainRun d (h ++ [st]) → ChainStep d st st' → ChainRun d (h ++ [st, st'])

def eventsAlong (d : Deployment) : List ChainState → List Event
  | st :: st' :: rest => eventsOf d st st' ++ eventsAlong d (st' :: rest)
  | _ => []

/-- A write log and the current slot as model events: before each write, a
`tick` for each slot since the previous write; then ticks up to `slot`. -/
def historyEvents (log : List (ℕ × ℕ × ℕ × ℕ)) (slot : ℕ) : List Event :=
  let r := log.foldl (fun (acc : List Event × ℕ) w =>
    (acc.1 ++ List.replicate (w.2.2.1 - acc.2) Event.tick ++ [Event.rootWrite w.1 w.2.1 w.2.2.2],
     max acc.2 w.2.2.1)) ([], 0)
  r.1 ++ List.replicate (slot - r.2) Event.tick

/-- The model events that build the deployed state: the chain's EIP-8272 writes
and slots up to deployment, then the balance the pool holds at deployment. -/
def initEvents (d : Deployment) : List Event :=
  historyEvents (chainInit d).rootWrites (chainInit d).slot ++
    [.receive ((chainInit d).balance (addrOf d))]

/-- The model events of a chain run from deployment. -/
def modelEvents (d : Deployment) (h : List ChainState) : List Event :=
  initEvents d ++ eventsAlong d h

def ReachableChain (d : Deployment) (st : ChainState) : Prop := ∃ h, ChainRun d h ∧ h.getLast? = some st

/-- Refinement, which also gives C5f and C7. For every extractor, along every chain run
the events its steps denote form a run of the model whose state the chain
shows, or the run has a bad event; if the model cannot follow some event, the
run up to and including that event has a bad event. `receive` accounts for
exactly the ETH that arrives other than by a call. -/
def Refines : Prop :=
  ∀ d ext, Honest d → ∀ h, ChainRun d h →
    ((∃ s, Run (poolOf d ext) (modelEvents d h) s ∧
        (BadEvent (poolOf d ext) (modelEvents d h) s ∨ Obs d (h.getLast?.getD default) s)) ∨
     ∃ pre e s, pre ++ [e] <+: modelEvents d h ∧ Run (poolOf d ext) pre s ∧
        BadEvent (poolOf d ext) (pre ++ [e]) s) ∧
    ∀ i st st', h[i]? = some st → h[i + 1]? = some st' →
      receivedIn (eventsOf d st st') = passiveInflow d st st'

opaque RawTxImpl : NonemptyType.{0}
/-- A concrete EIP-8141 transaction with EIP-8250's fields, as signed and encoded. -/
def RawTx : Type := RawTxImpl.type
/-- The fields of `FrameTx` a raw transaction carries, with resolved targets and
signers; `maxCost` is its `TXPARAM(0x06)`. -/
opaque RawTx.view : RawTx → FrameTx

/-- P5 to P7: `t` is valid in `st`. -/
opaque ValidTx : ChainState → RawTx → Prop
/-- The validity conditions frame 1 and later frames do not decide: EIP-8141's
static rules and gas caps, EIP-8250's decoding rules, EIP-1559's fee-field
checks, the fee caps against the base fee, the reservations
of each gas dimension against the block's remaining gas, the chain ID,
EIP-8250's nonce sequences, signature validation, and success of every frame
before frame 1. -/
opaque PreValid : ChainState → RawTx → Prop
/-- Every `APPROVE` that does not revert its frame, executed while `t` runs from
`st` by code whose `ADDRESS` is the pool's, in any frame: its frame index and
scope. -/
opaque approvalsIn : Deployment → ChainState → RawTx → List (ℕ × ℕ)

/-- C2. The pool's code approves only in frame 1 of its own transactions, with
scope 3, and only what `Acc` describes. -/
def C2 : Prop :=
  ∀ d st t, Honest d → ReachableChain d st → ValidTx st t →
    ∀ ap ∈ approvalsIn d st t,
      ap = (1, 3) ∧ t.view.sender = addrOf d ∧ Acc (addrOf d) (chainOf d) (verifierOf d) 1 t.view

/-- C2c. Given enough validation gas and balance, the pool approves every
transaction `Acc` describes that is valid up to frame 1, which makes it valid.
216,141 is frame 1's measured minimum under `G` (each nested call keeps back
1/64 of its gas); 195,840 is EIP-8250's first-use state gas for two keys. -/
def C2c : Prop :=
  ∀ d st t, Honest d → ReachableChain d st → PreValid st t →
    Acc (addrOf d) (chainOf d) (verifierOf d) 1 t.view →
    216141 ≤ (t.view.frames.getD 1 default).execLimit →
    195840 ≤ (t.view.frames.getD 1 default).stateLimit →
    t.view.maxCost ≤ st.balance (addrOf d) →
    ValidTx st t ∧ (1, 3) ∈ approvalsIn d st t

inductive Outcome | ok | reverted | outOfGas
deriving DecidableEq, Inhabited

/-- C9. The linked verifier returns 1 exactly when Groth16's verification for the
committed key accepts. -/
def C9 : Prop :=
  ∀ d, Honest d → ∀ π pub, π.length = 256 → (verifierOf d π pub ↔ Groth16Accepts π pub)

/-- `hash2` and `hash3` of the linked libraries: the returned word and the gas used. -/
opaque libHash2 : Deployment → F → F → Option (ℕ × ℕ)
opaque libHash3 : Deployment → F → F → F → Option (ℕ × ℕ)

/-- C8. The libraries return `H2` and `H3` within 200,000 gas. -/
def C8 : Prop :=
  ∀ d, Honest d →
    (∀ a b, ∃ g, libHash2 d a b = some ((H2 a b).val, g) ∧ g ≤ 200000) ∧
    (∀ a b c, ∃ g, libHash3 d a b c = some ((H3 a b c).val, g) ∧ g ≤ 200000)

opaque EnvImpl : NonemptyType.{0}
/-- A block header and transaction fields: number, timestamp, fee recipient,
prevrandao, base fee, gas limit and blob base fee, and the transaction's nonce,
gas price and fee caps. -/
def Env : Type := EnvImpl.type

/-- A non-frame EIP-1559 transaction from `caller`, with an empty access list,
no authorization list and no blobs, whose only call is one 36-byte call to the
pool, with value 0, a 16,000,000 gas limit and `env`'s fields, is valid in `st`: in the
current block with its header, or first in a next block whose header, `env`'s,
the consensus rules allow. -/
opaque EnvValid : ChainState → ℕ → Env → Prop

/-- The outcome of that transaction's call to the pool with the calldata. -/
opaque callPool : Deployment → ChainState → Env → ℕ → List UInt8 → Outcome

/-- The first `CALL`, `CALLCODE` or `STATICCALL` made during a `callPool` by code
whose `ADDRESS` is the pool's (a `DELEGATECALL` does not count): whether it is a
`CALL`, recipient, value, calldata, the execution gas the recipient's call frame
starts with (after EIP-150's 63/64 cap and including any value stipend, not the
gas operand), whether the value was transferred and execution at the recipient began (its
code, its EIP-7702 delegate's code, or a precompile), whether it succeeded, and
the size of its return data. -/
structure Payout where
  isCall : Bool
  recipient : ℕ
  value : ℕ
  data : List UInt8
  gas : ℕ
  entered : Bool
  success : Bool
  returnSize : ℕ

opaque firstPayout : Deployment → ChainState → Env → ℕ → List UInt8 → Option Payout

def publishCalldata (e : ℕ) : List UInt8 := [0xd0, 0x38, 0x70, 0xb3] ++ u256 e
def claimCalldata (r : ℕ) : List UInt8 := [0xa3, 0x06, 0x6a, 0xab] ++ u256 r

/-- The pool's first `CALL`, `CALLCODE` or `STATICCALL` is a plain payment of `v`
to `r` with at least 15,000,000 gas, and `r` rejected it or returned at least 64 KiB,
which the pool copies and which can exhaust its gas. A reentrancy guard in the
pool may make a recipient that calls back reject; that is allowed. -/
def RecipientRejected (d : Deployment) (st : ChainState) (env : Env) (caller r v : ℕ) : Prop :=
  ∃ po, firstPayout d st env caller (claimCalldata r) = some po ∧ po.isCall = true ∧
    po.recipient = r ∧ po.value = v ∧ po.data = [] ∧ 15000000 ≤ po.gas ∧ po.entered = true ∧
    (po.success = false ∨ 2 ^ 16 ≤ po.returnSize)

/-- C10. Anyone other than the pool, in any valid transaction and block
environment, can publish an existing epoch's nonzero root and pay out a covered
credit, which fails only if the recipient rejects a plain payment or returns at
least 64 KiB. -/
def C10 : Prop :=
  ∀ d st s caller env, Honest d → ReachableChain d st → Obs d st s → caller ≠ addrOf d →
    EnvValid st caller env →
    (∀ e ≤ s.E, (if e = s.E then TR (s.leaves s.E) else s.finalRoot e) ≠ 0 →
      callPool d st env caller (publishCalldata e) = .ok) ∧
    (∀ r < 2 ^ 160, 0 < s.credit r → s.credit r ≤ s.balance →
      callPool d st env caller (claimCalldata r) = .ok ∨
      RecipientRejected d st env caller r (s.credit r))

end

end MSP
