import Poseidon.Hash
import Keccak.Hash
import Mathlib.Algebra.BigOperators.Fin

/-!
# D2 to D9: hashes and the objects built from them
-/

namespace MSP

/-- D2. Concrete circomlib reference Poseidon over BN254. The irreducibility
attribute keeps symbolic proofs from expanding the rounds accidentally; the
definitions remain available for explicit unfolding and kernel checking.
Optimized-circuit equivalence is proved; deployed-library refinement remains open. -/
@[irreducible] def H2 (a b : F) : F := Poseidon.hash2 a b
@[irreducible] def H3 (a b c : F) : F := Poseidon.hash3 a b c
@[irreducible] def H10 (x : Fin 10 → F) : F := Poseidon.hash10 x

/-- D2. Concrete Ethereum Keccak-256, read as a big-endian natural. The
reference uses the legacy Keccak suffix and explicit kernel-computable rounds. -/
@[irreducible] def K (bytes : List UInt8) : ℕ := Keccak.hash bytes

theorem K_lt (bytes : List UInt8) : K bytes < 2^256 := by
  unfold K
  exact Keccak.hash_lt bytes

/-- D3. -/
def pk (sk : F) : F := H3 1 sk 0
def inner (sk ρ : F) : F := H2 (pk sk) ρ
def cm (i v : F) : F := H3 2 i v

/-- D4. -/
def DOMAIN_TAG : ℕ := K "minimal-shielded-pool:occurrence-domain:v1".toUTF8.toList
def D (c a e : ℕ) : F := (K (u256 DOMAIN_TAG ++ u256 c ++ u256 a ++ u256 e) : F)

/-- D5. The nullifier key and the nullifier. -/
def nfKey (d sk : F) : F := H2 d sk
def nf (d sk leaf : F) (i : ℕ) : F := H3 4 (nfKey d sk) (H2 leaf (i : F))

/-- D6. -/
def SINK (k : Fin 2) : F := cm ((k.val + 1 : ℕ) : F) 0

/-- D7. -/
def DEPTH : ℕ := 20

def Z : ℕ → F
  | 0 => 0
  | l + 1 => H2 (Z l) (Z l)

def EMPTY_ROOT : F := Z DEPTH

/-- D7. The root reached from `leaf` at index `i`: bit `l` of `i` puts the
running node on the right. -/
def MR (leaf : F) (i : ℕ) (sib : Fin DEPTH → F) : F :=
  (List.finRange DEPTH).foldl
    (fun cur l => if i.testBit l.val then H2 (sib l) cur else H2 cur (sib l)) leaf

/-- The root of a complete tree of height `h` whose leaves are `L` followed by zeros. -/
def treeRoot : ℕ → List F → F
  | 0, L => L.headD 0
  | h + 1, L => H2 (treeRoot h (L.take (2 ^ h))) (treeRoot h (L.drop (2 ^ h)))

/-- D7. -/
def TR (L : List F) : F := treeRoot DEPTH L

/-- D8. -/
structure Statement where
  nf1 : F
  nf2 : F
  o1 : F
  o2 : F
  root : F
  d : F
  pub : F
  fee : F
  rcp : F
  auth : F
deriving Inhabited, DecidableEq

def Statement.vec (x : Statement) : Fin 10 → F :=
  ![x.nf1, x.nf2, x.o1, x.o2, x.root, x.d, x.pub, x.fee, x.rcp, x.auth]

/-- D9. -/
def α (x : Statement) : F :=
  (K ((List.finRange 10).flatMap fun j => u256 (x.vec j).val) : F)
def β (x : Statement) : F := H10 x.vec
def γ (x : Statement) (s : F) : F := ∑ j : Fin 10, x.vec j * s ^ (j : ℕ)

end MSP
