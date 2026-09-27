import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
Pure, deliberately partial EVM opcode interpreter for a bounded dispatcher proof.
The stack order, opcode effects, memory expansion and gas equations are adapted
from Nethermind EVMYulLean commit 047f63070309f436b66c61e276ab3b6d1169265a,
EvmYul/{Semantics,MachineStateOps,EVM/{Semantics,Gas,PrimOps}}. See
UPSTREAM-LICENSE.txt (Apache-2.0, Copyright 2024 Demerzel Solutions Limited).

Changes: pure byte memory, terminating PUSH-aware jump scan, a frame-context
TXPARAM(2), and explicit refusal of unsupported opcodes. An absent code byte is
STOP; an unsupported byte inside code is an exception. This is not a complete
EVM, transaction validator, or definition of any Spec/Evm chain declaration.
-/

namespace MSP.Chain.Pilot

abbrev Word := ZMod (2 ^ 256)
abbrev Memory := ℕ → UInt8

/-- Presence means that execution is inside a frame transaction. Its validation
and frame-entry accounting are outside this opcode interpreter. -/
structure FrameContext where
  sender : Word

structure Env where
  code : List UInt8
  address : Word
  calldata : List UInt8
  frame : Option FrameContext
  /-- Execution gas charged by TXPARAM; supplied by the pinned fork profile. -/
  txparamGas : ℕ

/-- Persistent state and approvals are explicit carried state. None of the
implemented instructions can change them. Memory and the stack are local. -/
structure Machine (Persistent : Type) where
  pc : ℕ
  stack : List Word
  memory : Memory
  activeWords : ℕ
  executionGas : ℕ
  stateGas : ℕ
  persistent : Persistent
  approvals : List ℕ

inductive Fault where
  | unsupportedOpcode (byte : UInt8)
  | unsupportedTxparam (selector : Word)
  | outsideFrameTransaction
  | stackUnderflow
  | stackOverflow
  | badJump
  | outOfGas
  | outOfFuel
  deriving DecidableEq, Repr

inductive Outcome (Persistent : Type) where
  | running (machine : Machine Persistent)
  | stopped (machine : Machine Persistent) (output : List UInt8)
  | reverted (machine : Machine Persistent) (output : List UInt8)
  | exceptional (fault : Fault)

inductive Instr where
  | stop | push (width : ℕ) | calldatasize | eq | address | txparam
  | sub | jumpi | jump | jumpdest | shl | mstore | revert
  deriving DecidableEq, Repr

def pushWidth (b : UInt8) : ℕ :=
  if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then b.toNat - 0x5f else 0

def decode (code : List UInt8) (pc : ℕ) : Except Fault Instr :=
  match code[pc]? with
  | none => .ok .stop
  | some b =>
    if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then .ok (.push (pushWidth b))
    else match b.toNat with
    | 0x00 => .ok .stop
    | 0x03 => .ok .sub
    | 0x14 => .ok .eq
    | 0x1b => .ok .shl
    | 0x30 => .ok .address
    | 0x36 => .ok .calldatasize
    | 0x52 => .ok .mstore
    | 0x56 => .ok .jump
    | 0x57 => .ok .jumpi
    | 0x5b => .ok .jumpdest
    | 0x5f => .ok (.push 0)
    | 0xb0 => .ok .txparam
    | 0xfd => .ok .revert
    | _ => .error (.unsupportedOpcode b)

/-- Scan up to the requested target. Every non-PUSH byte advances one byte,
including bytes this partial interpreter does not implement. Thus unknown
opcodes cannot hide a later JUMPDEST, and PUSH data never become destinations.
The target bounds the number of iterations, so the scan is total. -/
def jumpScan (target : ℕ) : ℕ → ℕ → List UInt8 → Bool
  | 0, _, _ => false
  | fuel+1, pc, code =>
    if pc > target then false else
    match code with
    | [] => false
    | b :: rest =>
      if pc = target then b == 0x5b
      else jumpScan target fuel (pc + 1 + pushWidth b) (rest.drop (pushWidth b))

def validJump (code : List UInt8) (target : ℕ) : Bool :=
  jumpScan target (target+1) 0 code

/-- EVM PUSH data is big-endian and missing bytes at code end are zero. -/
def pushValue (code : List UInt8) (pc width : ℕ) : Word :=
  ((List.range width).foldl (fun n j => n * 256 + (code[pc+1+j]?.getD 0).toNat) 0 : ℕ)

def wordsFor (current offset length : ℕ) : ℕ :=
  if length = 0 then current else max current ((offset + length + 31) / 32)

def memoryCost (words : ℕ) : ℕ := 3 * words + words * words / 512

def expansionCost (current offset length : ℕ) : ℕ :=
  memoryCost (wordsFor current offset length) - memoryCost current

def writeWord (memory : Memory) (offset : ℕ) (value : Word) : Memory := fun i =>
  if offset ≤ i ∧ i < offset+32 then
    UInt8.ofNat (value.val / 256 ^ (31 - (i-offset)) % 256)
  else memory i

def memorySlice (memory : Memory) (offset length : ℕ) : List UInt8 :=
  (List.range length).map fun i => memory (offset+i)

def advance (s : Machine P) (pc : ℕ) (stack : List Word) : Outcome P :=
  if stack.length ≤ 1024 then .running { s with pc := pc, stack := stack }
  else .exceptional .stackOverflow

def charged (s : Machine P) (cost : ℕ) (next : Machine P → Outcome P) : Outcome P :=
  if cost ≤ s.executionGas then next { s with executionGas := s.executionGas - cost }
  else .exceptional .outOfGas

/-- A single opcode, with top-of-stack first. JUMPI checks its target only when
the condition is nonzero. SUB and SHL retain EVM operand order. -/
def execute (env : Env) (instr : Instr) (s : Machine P) : Outcome P :=
  match instr with
  | .stop => .stopped s []
  | .push width => charged s (if width = 0 then 2 else 3) fun t =>
      advance t (s.pc + 1 + width) (pushValue env.code s.pc width :: s.stack)
  | .calldatasize => charged s 2 fun t =>
      advance t (s.pc+1) ((env.calldata.length : Word) :: s.stack)
  | .address => charged s 2 fun t => advance t (s.pc+1) (env.address :: s.stack)
  | .jumpdest => charged s 1 fun t => advance t (s.pc+1) s.stack
  | .eq | .sub | .shl =>
      match s.stack with
      | a :: b :: rest => charged s 3 fun t =>
          let value := match instr with
            | .eq => if a = b then 1 else 0
            | .sub => a - b
            | _ => if a.val ≥ 256 then 0 else b * (2 ^ a.val : ℕ)
          advance t (s.pc+1) (value :: rest)
      | _ => .exceptional .stackUnderflow
  | .txparam =>
      match s.stack, env.frame with
      | [], _ => .exceptional .stackUnderflow
      | _ :: _, none => .exceptional .outsideFrameTransaction
      | selector :: rest, some frame =>
          if selector = 2 then charged s env.txparamGas fun t =>
            advance t (s.pc+1) (frame.sender :: rest)
          else .exceptional (.unsupportedTxparam selector)
  | .jump =>
      match s.stack with
      | target :: rest => charged s 8 fun t =>
          if validJump env.code target.val then advance t target.val rest
          else .exceptional .badJump
      | _ => .exceptional .stackUnderflow
  | .jumpi =>
      match s.stack with
      | target :: cond :: rest => charged s 10 fun t =>
          if cond = 0 then advance t (s.pc+1) rest
          else if validJump env.code target.val then advance t target.val rest
          else .exceptional .badJump
      | _ => .exceptional .stackUnderflow
  | .mstore =>
      match s.stack with
      | offset :: value :: rest =>
          charged s (3 + expansionCost s.activeWords offset.val 32) fun t =>
            advance { t with memory := writeWord s.memory offset.val value,
                             activeWords := wordsFor s.activeWords offset.val 32 }
              (s.pc+1) rest
      | _ => .exceptional .stackUnderflow
  | .revert =>
      match s.stack with
      | offset :: length :: rest =>
          charged s (expansionCost s.activeWords offset.val length.val) fun t =>
            .reverted { t with stack := rest,
                                pc := s.pc+1,
                                activeWords := wordsFor s.activeWords offset.val length.val }
              (memorySlice s.memory offset.val length.val)
      | _ => .exceptional .stackUnderflow

def step (env : Env) (s : Machine P) : Outcome P :=
  match decode env.code s.pc with
  | .error e => .exceptional e
  | .ok instr => execute env instr s

def run (env : Env) : ℕ → Machine P → Outcome P
  | 0, _ => .exceptional .outOfFuel
  | n+1, s => match step env s with
    | .running t => run env n t
    | result => result

end MSP.Chain.Pilot
