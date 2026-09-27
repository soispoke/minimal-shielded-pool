import Proofs.NonVacuityKeccakTable
import Proofs.NonVacuityFixtureQueries
import Proofs.NonVacuityPoseidon

/-! Match the W1 transaction/root messages to the checked concrete Keccak
preimages. Numeric Poseidon facts are used only to identify these bytes. -/

namespace MSP.NonVacuity

attribute [local irreducible] Keccak.hash D

private theorem data_nf1 : fixtureData.nf1 =
    2078667565048261126995952142193965014036398664970972851055714654440913762076 := by
  change fixtureStatement.nf1.val = _
  rw [fixture_nf1_eq]
  decide

private theorem data_nf2 : fixtureData.nf2 =
    14733247219625856291985193582540913734334269146722451096619511141630182331973 := by
  change fixtureStatement.nf2.val = _
  rw [fixture_nf2_eq]
  decide

private theorem data_root : fixtureData.root =
    4672675675891064292615413573032888530994442186079076763921881607647678868115 := by
  change fixtureStatement.root.val = _
  rw [fixture_statement_root_eq]
  decide

theorem fixtureNonceMsg_eq : fixtureNonceMsg = KeccakData.nonce.input := by
  unfold fixtureNonceMsg
  rw [data_nf1, data_nf2]
  decide

theorem fixtureEntryMsg_eq : fixtureEntryMsg = KeccakData.entry.input := by
  unfold fixtureEntryMsg rrEntryMsg
  rw [sourceId_one_zero_eq, rr_entry_domain_eq, data_root]
  rfl

theorem fixtureKeyMsg_eq : fixtureKeyMsg = KeccakData.key.input := by
  unfold fixtureKeyMsg rrKeyMsg
  rw [sourceId_one_zero_eq, rr_storage_domain_eq]
  rfl

theorem fixtureCreditMsg_eq : creditMsg 1 = KeccakData.credit.input := rfl

/-- Exactly the six distinct non-Poseidon inputs in the compact W1 trace. -/
noncomputable def fixtureKeccakQueries : List Query :=
  [.dom 1 1 0, .keccak (addr20 1 ++ u256 0), .keccak fixtureNonceMsg,
   .keccak fixtureEntryMsg, .keccak fixtureKeyMsg, .keccak (creditMsg 1)]

theorem fixtureKeccakTable_support : ∀ q ∈ fixtureKeccakQueries,
    ∃ n, (q, n) ∈ fixtureKeccakTable := by
  intro q h
  simp only [fixtureKeccakQueries, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨4968480372713856270053508398811659268951190880053845541428304835575363535147, by simp [fixtureKeccakTable]⟩
  · exact ⟨83777132435126701296934365153674188610954941488820807845617732241460198689413, by simp [fixtureKeccakTable]⟩
  · rw [fixtureNonceMsg_eq]
    exact ⟨105172361973511582508073143921805373148050156884159367960169935661850780820418, by simp [fixtureKeccakTable]⟩
  · rw [fixtureEntryMsg_eq]
    exact ⟨36844462081589758283229017563449643654917470375464070248113247160864747215828, by simp [fixtureKeccakTable]⟩
  · rw [fixtureKeyMsg_eq]
    exact ⟨32038931655532369272810969708519453443812429929528782484501449200405960908960, by simp [fixtureKeccakTable]⟩
  · rw [fixtureCreditMsg_eq]
    exact ⟨110105352452153409464507274423846025220818648551547185850537974539897514851215, by simp [fixtureKeccakTable]⟩

#print axioms fixtureNonceMsg_eq
#print axioms fixtureEntryMsg_eq
#print axioms fixtureKeccakTable_support

end MSP.NonVacuity
