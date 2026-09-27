import Proofs.NonVacuityFixtureRun
import Proofs.NonVacuityFixtureTable

namespace MSP.NonVacuity

noncomputable section

def fixtureNonceMsg : List UInt8 :=
  u256 2 ++ u256 (min fixtureData.nf1 fixtureData.nf2) ++
    u256 (max fixtureData.nf1 fixtureData.nf2)

def fixtureEntryMsg : List UInt8 := rrEntryMsg (sourceId 1 0) 0 fixtureData.root
def fixtureKeyMsg : List UInt8 := rrKeyMsg (sourceId 1 0) 0

/-- The candidate's exact compact trace. Repeated entries deliberately remain
present; the certificate table may cover several occurrences with one entry. -/
def fixtureQueries : List Query :=
  [.h3 2 1 0, .h3 2 2 0] ++ [.h3 2 fixtureInner 2] ++
  witnessQueries fixtureStatement fixtureWitness ++
  [.dom 1 1 0, .keccak (addr20 1 ++ u256 0),
   .keccak fixtureNonceMsg, .keccak fixtureNonceMsg,
   .keccak fixtureEntryMsg, .keccak fixtureKeyMsg] ++
  [.keccak (creditMsg 1)] ++
  [.keccak fixtureEntryMsg, .keccak fixtureKeyMsg] ++
  [.dom 1 1 0, .keccak (addr20 1 ++ u256 0)] ++
  compactQueries DEPTH [] ++ compactQueries DEPTH [fixtureLeaf]

theorem fixture_queries_eq (a : Assignment) (tx : FrameTx)
    (hsd : settleData tx = fixtureData) (hkeys : tx.nonceKeys = fixtureKeys)
    (hpub : verifiedPublics tx = publicOf a)
    (hx : stmtOf a = fixtureStatement) (hw : witOf a = fixtureWitness) :
    compactTraceQueries (idealPool 1 1 a) (fixtureEvents ++ [.spend tx 1]) fixtureSettled =
      fixtureQueries := by
  have he : eventQueries (idealPool 1 1 a) (.spend tx 1) =
      witnessQueries fixtureStatement fixtureWitness ++
      [.dom 1 1 0, .keccak (addr20 1 ++ u256 0),
       .keccak fixtureNonceMsg, .keccak fixtureNonceMsg,
       .keccak fixtureEntryMsg, .keccak fixtureKeyMsg] ++ [.keccak (creditMsg 1)] := by
    simp [eventQueries, extOf, hpub, hx, hw, hsd, hkeys,
      idealPool, fixtureKeys, fixtureData, fixtureNonceMsg, fixtureEntryMsg,
      fixtureKeyMsg, List.append_assoc]
  have hl : fixtureSettled.leaves 0 = [fixtureLeaf] := fixture_shielded_leaves
  have hr : fixtureSettled.roots = [(sourceId 1 0, 0, fixtureData.root)] := rfl
  have hep : fixtureSettled.E = 0 := fixture_ready_epoch
  simp only [compactTraceQueries, fixtureEvents, List.cons_append, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, he,
    hr, hep]
  simp [eventQueries, fixtureQueries, fixtureEntryMsg, fixtureKeyMsg, List.append_assoc,
    List.range_succ, hl, idealPool]

end
end MSP.NonVacuity
