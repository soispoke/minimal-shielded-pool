import Spec.Basic
import Mathlib.Tactic.Linarith

/-! Ethereum Keccak-256: Keccak-f[1600], rate 1088, capacity 512,
legacy delimited suffix 0x01, and pad10*1. Lanes and their bytes are little
endian; the resulting 32 digest bytes are read as a big-endian natural for K.

The permutation follows the Keccak team's reference (v3.0, §1), with lane
index x + 5*y. This is a concrete reference definition, not a security claim.
-/

namespace MSP.Keccak

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev Lane := BitVec 64
abbrev State := Vector Lane 25

def roundConstants : Vector Lane 24 := ⟨#[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008], rfl⟩

def rotations : Vector ℕ 25 := ⟨#[
  0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
  41, 45, 15, 21, 8, 18, 2, 61, 56, 14], rfl⟩

def lane (s : State) (x y : ℕ) : Lane :=
  s.get ⟨x % 5 + 5 * (y % 5), by omega⟩

def theta (s : State) : State :=
  let c : Vector Lane 5 := Vector.ofFn fun x =>
    lane s x.val 0 ^^^ lane s x.val 1 ^^^ lane s x.val 2 ^^^
      lane s x.val 3 ^^^ lane s x.val 4
  let d : Vector Lane 5 := Vector.ofFn fun x =>
    c.get ⟨(x.val + 4) % 5, by omega⟩ ^^^
      (c.get ⟨(x.val + 1) % 5, by omega⟩).rotateLeft 1
  Vector.ofFn fun i => s.get i ^^^ d.get ⟨i.val % 5, by omega⟩

/-- Inverse indexing of B[y,2*x+3*y] = rot(A[x,y],r[x,y]). -/
def rhoPi (s : State) : State := Vector.ofFn fun i =>
  let x := (i.val % 5 + 3 * (i.val / 5)) % 5
  let y := i.val % 5
  let j : Fin 25 := ⟨x + 5 * y, by omega⟩
  (s.get j).rotateLeft (rotations.get j)

def chi (s : State) : State := Vector.ofFn fun i =>
  let x := i.val % 5
  let y := i.val / 5
  lane s x y ^^^ ((~~~(lane s (x+1) y)) &&& lane s (x+2) y)

def round (s : State) (rc : Lane) : State :=
  let b := chi (rhoPi (theta s))
  Vector.ofFn fun i => if i.val = 0 then b.get i ^^^ rc else b.get i

def rounds : ℕ → State → State
  | 0, s => s
  | n+1, s => round (rounds n s) (roundConstants.get ⟨n % 24, by omega⟩)

def permute (s : State) : State := rounds 24 s

def zeroState : State := Vector.replicate 25 0

/-- No SHA3 suffix bits are appended. At a 135-byte remainder both pad bits
occupy one byte (0x81); at a multiple of 136 an entire pad block is appended. -/
def pad (input : List UInt8) : List UInt8 :=
  if input.length % 136 = 135 then input ++ [0x81]
  else input ++ [0x01] ++ List.replicate (134 - input.length % 136) 0 ++ [0x80]

def loadLane (bytes : List UInt8) : Lane :=
  BitVec.ofNat 64 (((bytes.take 8).reverse).foldl (fun n b => n * 256 + b.toNat) 0)

def absorbBlock (s : State) (block : List UInt8) : State :=
  Vector.ofFn fun i =>
    if i.val < 17 then s.get i ^^^ loadLane (block.drop (8*i.val)) else s.get i

def absorbBlocks : ℕ → List UInt8 → State → State
  | 0, _, s => s
  | n+1, bytes, s =>
    absorbBlocks n (bytes.drop 136) (permute (absorbBlock s (bytes.take 136)))

def finalState (input : List UInt8) : State :=
  let bytes := pad input
  absorbBlocks (bytes.length / 136) bytes zeroState

/-- The first 32 sponge bytes; no additional permutation is needed to squeeze
32 bytes from a 136-byte rate. -/
def squeeze (s : State) : Vector UInt8 32 := Vector.ofFn fun i =>
  UInt8.ofNat ((s.get ⟨i.val / 8, by omega⟩).toNat / 256 ^ (i.val % 8) % 256)

def digest (input : List UInt8) : Vector UInt8 32 := squeeze (finalState input)

def readBE : List UInt8 → ℕ
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + readBE bs

/-- D2's digest interpreted as a big-endian word. -/
def hash (input : List UInt8) : ℕ := readBE (digest input).toList

theorem digest_length (input : List UInt8) : (digest input).toList.length = 32 := by simp

theorem readBE_lt (bytes : List UInt8) : readBE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [readBE]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt_size
    simp only [readBE, List.length_cons, pow_succ]
    nlinarith

theorem hash_lt (input : List UInt8) : hash input < 2^256 := by
  have h := readBE_lt (digest input).toList
  change readBE (digest input).toList < 2^256
  rw [digest_length] at h
  exact h

attribute [local irreducible] hash

def word (input : List UInt8) : BitVec 256 := ⟨hash input, hash_lt input⟩

theorem word_toNat (input : List UInt8) : (word input).toNat = hash input :=
  BitVec.toNat_ofFin ⟨hash input, hash_lt input⟩

theorem pad_length (input : List UInt8) :
    (pad input).length = 136 * (input.length / 136 + 1) := by
  have hm := Nat.mod_lt input.length (by decide : 0 < 136)
  have hd := Nat.mod_add_div input.length 136
  unfold pad
  split <;> simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate] <;> omega

theorem pad_blocks_positive (input : List UInt8) : 0 < (pad input).length / 136 := by
  rw [pad_length, Nat.mul_div_right _ (by decide : 0 < 136)]
  omega

end MSP.Keccak
