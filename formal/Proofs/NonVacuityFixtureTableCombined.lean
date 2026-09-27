import Proofs.NonVacuityPoseidonTable
import Proofs.NonVacuityKeccakTable

/-! The complete finite output table, including cross-table collisions. -/

namespace MSP.NonVacuity

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def fixtureTable : List (Query × ℕ) := poseidonTable ++ fixtureKeccakTable

theorem fixtureTable_values (q : Query) (n : ℕ) (h : (q, n) ∈ fixtureTable) :
    queryValue q = n := by
  rcases List.mem_append.mp h with hp | hk
  · exact poseidonTable_values q n hp
  · exact fixtureKeccakTable_values q n hk

theorem fixtureTable_large (q : Query) (n : ℕ) (h : (q, n) ∈ fixtureTable) :
    2 ^ 64 ≤ n := by
  rcases List.mem_append.mp h with hp | hk
  · exact poseidonTable_large q n hp
  · exact fixtureKeccakTable_large q n hk

theorem fixtureTable_unique : TableUnique fixtureTable := by
  apply tableUnique_of_pairwise
  decide

#print axioms fixtureTable_values
#print axioms fixtureTable_large
#print axioms fixtureTable_unique

end MSP.NonVacuity
