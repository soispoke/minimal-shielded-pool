import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# D1: fields, words and byte encodings

The Lean statements mirror `formal/SPEC.md`. They prove no claim and contain
no `sorry`: each claim is a `Prop` that later steps prove, and the only proofs
are helpers such as `NeZero p` and `K_lt`.
-/

namespace MSP

/-- D1. The BN254 scalar field order. -/
def p : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- D1. The BN254 base field order, which bounds proof point coordinates. -/
def q : ℕ := 21888242871839275222246405745257275088696311157297823662689037894645226208583

instance : NeZero p := ⟨by norm_num [p]⟩

abbrev F := ZMod p

/-- Big-endian encoding of `n mod 256 ^ k` in `k` bytes. -/
def be (k n : ℕ) : List UInt8 :=
  (List.range k).reverse.map fun j => UInt8.ofNat (n / 256 ^ j % 256)

def u256 (n : ℕ) : List UInt8 := be 32 n
def u64be (n : ℕ) : List UInt8 := be 8 n
def addr20 (a : ℕ) : List UInt8 := be 20 a

/-- The 32-byte big-endian word at `off`, reading missing bytes as zero,
as `CALLDATALOAD` and EIP-8141's frame data load do. -/
def wordAt (d : List UInt8) (off : ℕ) : ℕ :=
  (((d.drop off).take 32) ++ List.replicate 32 0).take 32
    |>.foldl (fun (acc : ℕ) (b : UInt8) => acc * 256 + b.toNat) 0

end MSP
