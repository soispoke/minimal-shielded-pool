import Spec.Hash

/-!
# D11 and D15: frame transactions and what the pool accepts
-/

namespace MSP

inductive Mode | default | verify | sender
deriving DecidableEq, Inhabited

/-- D11. One frame, with its resolved target and, once it has run, its status. -/
structure Frame where
  target : ℕ
  mode : Mode
  flags : ℕ
  value : ℕ
  execLimit : ℕ
  stateLimit : ℕ
  data : List UInt8
  status : Bool
deriving Inhabited

/-- D11. `msg` is empty (the signature signs the canonical hash) or a nonzero
32-byte digest (P5). -/
structure Signature where
  scheme : ℕ
  signer : ℕ
  msg : List UInt8
deriving Inhabited

/-- D11. EIP-8141 with EIP-8250's `nonce_keys` and `nonce_seq`. -/
structure FrameTx where
  chainId : ℕ
  nonceKeys : List ℕ
  nonceSeq : ℕ
  sender : ℕ
  frames : List Frame
  signatures : List Signature
  blobHashes : List ℕ
  maxCost : ℕ
deriving Inhabited

/-- P5. `TXPARAM(0x0F)`: EIP-8250's hash of the key set. -/
def keysHash (ks : List ℕ) : ℕ := K (u256 ks.length ++ ks.flatMap u256)

def RECENT_ROOT : ℕ := 0x8272
def SETTLE_SELECTOR : List UInt8 := [0x92, 0x1f, 0xca, 0xc7]

/-- EIP-8272's source for the pool's epoch `e` (`sourceId` in the dispatcher). -/
def sourceId (a e : ℕ) : ℕ := K (addr20 a ++ u256 e)

def RR_ENTRY_DOMAIN : ℕ := K "RECENT_ROOT_ENTRY".toUTF8.toList
def RR_STORAGE_DOMAIN : ℕ := K "RECENT_ROOT_STORAGE".toUTF8.toList

/-- EIP-8272: the Keccak input of the entry committed for `(source, slot, root)`. -/
def rrEntryMsg (src sl root : ℕ) : List UInt8 := u256 RR_ENTRY_DOMAIN ++ u256 src ++ u64be sl ++ u256 root

/-- EIP-8272: the Keccak input of the storage key of ring index `i` of `source`. -/
def rrKeyMsg (src i : ℕ) : List UInt8 := u256 RR_STORAGE_DOMAIN ++ u256 src ++ u64be i

/-- The Keccak inputs of the logic's storage slots `withdrawalCredit[r]` (slot 23)
and `finalRoot[e]` (slot 25). -/
def creditMsg (r : ℕ) : List UInt8 := u256 r ++ u256 23
def finalRootMsg (e : ℕ) : List UInt8 := u256 e ++ u256 25

/-- The settlement data words after the selector, in the `Spend` order. -/
structure SettleData where
  root : ℕ
  rootSlot : ℕ
  epoch : ℕ
  domain : ℕ
  nf1 : ℕ
  nf2 : ℕ
  o1 : ℕ
  o2 : ℕ
  pub : ℕ
  fee : ℕ
  rcp : ℕ
  auth : ℕ

def SettleData.decode (d : List UInt8) : SettleData :=
  ⟨wordAt d 4, wordAt d 36, wordAt d 68, wordAt d 100, wordAt d 132, wordAt d 164,
   wordAt d 196, wordAt d 228, wordAt d 260, wordAt d 292, wordAt d 324, wordAt d 356⟩

/-- D8. The statement the settlement data denotes, read as field elements. -/
def SettleData.stmt (s : SettleData) : Statement :=
  ⟨s.nf1, s.nf2, s.o1, s.o2, s.root, s.domain, s.pub, s.fee, s.rcp, s.auth⟩

/-- A6. None of the proof's points `A`, `B`, `C` is encoded as the point at infinity. -/
def PointsNotInfinity (π : List UInt8) : Prop :=
  (wordAt π 0 ≠ 0 ∨ wordAt π 32 ≠ 0) ∧
  (wordAt π 64 ≠ 0 ∨ wordAt π 96 ≠ 0 ∨ wordAt π 128 ≠ 0 ∨ wordAt π 160 ≠ 0) ∧
  (wordAt π 192 ≠ 0 ∨ wordAt π 224 ≠ 0)

/-- P5 and P12. `tx` carries a secp256k1 signature by `signer` with empty `msg`,
which the protocol validated over the canonical signature hash. -/
def SignsCanonicalHash (tx : FrameTx) (signer : ℕ) : Prop :=
  ∃ sg ∈ tx.signatures, sg.scheme = 1 ∧ sg.msg = [] ∧ sg.signer = signer

/-- D15. The pool at `A` on chain `c` accepts `tx` in its frame 1.
`verifies π pub` means the linked verifier's return value for proof words `π`
and public signals `pub` is exactly 1; whether 500,000 gas suffices is C2c's
concern. `current` is the executing
frame index. -/
def Acc (A c : ℕ) (verifies : List UInt8 → F × F × F → Prop) (current : ℕ) (tx : FrameTx) : Prop :=
  ∃ f0 f1 f2 : Frame, ∃ rest : List Frame,
    tx.frames = f0 :: f1 :: f2 :: rest ∧ rest.length ≤ 1 ∧
    let s := SettleData.decode f2.data
    let x := s.stmt
    let π := f1.data.take 256
    let b := wordAt f1.data 256
    -- A1
    (tx.sender = A ∧ tx.signatures.length = 1 ∧ tx.blobHashes = [] ∧ current = 1 ∧
     f0.target = RECENT_ROOT ∧ f0.mode = .verify ∧ f0.flags = 0 ∧ f0.data.length = 72 ∧
     f0.status = true ∧ f0.value = 0 ∧ f0.stateLimit = 0 ∧
     f1.target = A ∧ f1.mode = .verify ∧ f1.flags = 3 ∧ f1.data.length = 288 ∧ f1.value = 0 ∧
     f2.target = A ∧ f2.mode = .sender ∧ f2.flags = 0 ∧ f2.data.length = 388 ∧
     f2.data.take 4 = SETTLE_SELECTOR ∧ f2.value = 0 ∧
     f2.execLimit = 2000000 ∧ f2.stateLimit = 550000 ∧
     (∀ f3 ∈ rest, f3.target ≠ 0 ∧ f3.mode = .default ∧ f3.flags = 0 ∧ f3.value = 0)) ∧
    -- A2: the checks the dispatcher makes; C3 derives the key list from them
    (tx.nonceSeq = 0 ∧ tx.nonceKeys.length = 2 ∧
     keysHash tx.nonceKeys = K (u256 2 ++ u256 (min s.nf1 s.nf2) ++ u256 (max s.nf1 s.nf2))) ∧
    -- A3
    (s.epoch < 2 ^ 64 ∧ s.rootSlot < 2 ^ 64 ∧
     f0.data = u256 (sourceId A s.epoch) ++ u64be s.rootSlot ++ u256 s.root) ∧
    -- A4
    (∃ sg, tx.signatures = [sg] ∧ sg.scheme = 1 ∧ sg.msg = [] ∧ sg.signer = s.auth) ∧
    -- A5
    (s.nf1 ≠ 0 ∧ s.nf2 ≠ 0 ∧ s.root < p ∧ s.domain < p ∧ s.nf1 < p ∧ s.nf2 < p ∧
     s.o1 < p ∧ s.o2 < p ∧ s.pub < 2 ^ 128 ∧ s.fee < 2 ^ 128 ∧ s.rcp < 2 ^ 160 ∧
     0 < s.auth ∧ s.auth < 2 ^ 160 ∧ (s.pub = 0 ↔ s.rcp = 0) ∧
     s.domain = (D c A s.epoch).val) ∧
    -- A6
    ((∀ j < 8, wordAt π (32 * j) < q) ∧ PointsNotInfinity π ∧ b < p ∧
     verifies π ((b : F), γ x (α x + b), α x)) ∧
    -- A7
    tx.maxCost ≤ s.fee

end MSP
