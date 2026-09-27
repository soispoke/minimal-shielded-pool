import Proofs.NonVacuityFixtureTable
import Proofs.NonVacuityKeccak
import Proofs.NonVacuityKeccakNonceData
import Proofs.NonVacuityKeccakEntryData
import Proofs.NonVacuityKeccakKeyData
import Proofs.NonVacuityKeccakCreditData

/-! Six exact non-Poseidon queries of the W1 candidate. The input bytes and
outputs here are concrete. Separate semantic bindings identify the fixture's
nonce/root messages with these bytes, using the checked Poseidon constants. -/

namespace MSP.NonVacuity

attribute [local irreducible] Keccak.hash

def fixtureKeccakTable : List (Query × ℕ) :=
  [(.keccak (addr20 1 ++ u256 0),
      83777132435126701296934365153674188610954941488820807845617732241460198689413),
   (.keccak KeccakData.nonce.input,
      105172361973511582508073143921805373148050156884159367960169935661850780820418),
   (.keccak KeccakData.entry.input,
      36844462081589758283229017563449643654917470375464070248113247160864747215828),
   (.keccak KeccakData.key.input,
      32038931655532369272810969708519453443812429929528782484501449200405960908960),
   (.keccak KeccakData.credit.input,
      110105352452153409464507274423846025220818648551547185850537974539897514851215),
   (.dom 1 1 0,
      4968480372713856270053508398811659268951190880053845541428304835575363535147)]

theorem fixtureKeccakTable_values :
    ∀ q n, (q, n) ∈ fixtureKeccakTable → queryValue q = n := by
  intro q n h
  simp only [fixtureKeccakTable, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> cases h
  · exact sourceId_one_zero_eq
  · change K KeccakData.nonce.input = _
    unfold K
    exact KeccakData.nonce.hash_eq
  · change K KeccakData.entry.input = _
    unfold K
    exact KeccakData.entry.hash_eq
  · change K KeccakData.key.input = _
    unfold K
    exact KeccakData.key.hash_eq
  · change K KeccakData.credit.input = _
    unfold K
    exact KeccakData.credit.hash_eq
  · exact domain_one_one_zero_val

theorem fixtureKeccakTable_unique : TableUnique fixtureKeccakTable := by
  apply tableUnique_of_pairwise
  decide

theorem fixtureKeccakTable_large :
    ∀ q n, (q, n) ∈ fixtureKeccakTable → 2^64 ≤ n := by
  intro q n h
  simp only [fixtureKeccakTable, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> cases h <;> decide

#print axioms fixtureKeccakTable_values
#print axioms fixtureKeccakTable_unique
#print axioms fixtureKeccakTable_large

end MSP.NonVacuity
