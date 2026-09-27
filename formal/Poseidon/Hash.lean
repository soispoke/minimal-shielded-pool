import Poseidon.Constants

/-! Concrete reference functions used by `Spec.Hash`'s H2, H3 and H10.
Equivalence with the optimized circuit is proved; equivalence with the deployed
libraries is part of C8 (step 5). -/

namespace MSP.Poseidon

def hash2 (a b : F) : F := hash params3 ⟨#[a, b], rfl⟩

def hash3 (a b c : F) : F := hash params4 ⟨#[a, b, c], rfl⟩

def hash10 (inputs : Fin 10 → F) : F := hash params11 (Vector.ofFn inputs)

/-- The recursive zero hashes needed to check C6's contract constants. -/
def zeroHash : ℕ → F
  | 0 => 0
  | n + 1 => let z := zeroHash n; hash2 z z

end MSP.Poseidon
