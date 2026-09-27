import Proofs.NonVacuityFixtureIdeal
import Sanity.SpendableR
import Sanity.TreeLemma

/-! Fixed W1 candidate: shield two units at epoch/index zero, withdraw one,
pay one as gas, and use the two designated sinks for both zero-valued outputs.
The remaining finite hash inequalities are explicit until the subsequent
numeric certificate modules discharge them. -/

namespace MSP.NonVacuity

noncomputable section
open Classical

def fixtureParameters : Pool := ⟨1, 1, fun _ _ => False, fun _ _ => default⟩
def fixtureInner : F := inner 1 1
def fixtureLeaf : F := cm fixtureInner 2
def fixtureSpend : Statement × Witness :=
  mkSpend fixtureParameters 0 [fixtureLeaf] 0 1 1 2 2 2 1 1 1
def fixtureStatement : Statement := fixtureSpend.1
def fixtureWitness : Witness := fixtureSpend.2

theorem siblings_singleton_zero (leaf : F) (l : Fin DEPTH) :
    siblingsOf [leaf] 0 l = Z l.val := by
  unfold siblingsOf
  simp only [Nat.zero_div, Nat.zero_xor, one_mul]
  have hp : 0 < 2 ^ l.val := by positivity
  have hd : ([leaf] : List F).drop (2 ^ l.val) = [] := by
    apply List.drop_eq_nil_of_le
    change 1 ≤ 2 ^ l.val
    omega
  rw [hd, List.take_nil, treeRoot_nil]

theorem fixture_real_siblings : fixtureWitness.sib 0 = fun l => Z l.val := by
  funext l
  exact siblings_singleton_zero fixtureLeaf l

theorem fixture_dummy_siblings : fixtureWitness.sib 1 = fun _ => 0 := rfl

theorem fixture_relation (hnf : fixtureStatement.nf1 ≠ fixtureStatement.nf2)
    (hsink : SINK 0 ≠ SINK 1) : R fixtureStatement fixtureWitness := by
  apply mkSpend_R fixtureParameters 0 [fixtureLeaf] 0 1 1 2 2 2 1 1 1
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro _
    have hm := MR_siblingsOf [fixtureLeaf] 0 (by decide)
    simpa [mkSpend, Witness.leaf, fixtureLeaf, fixtureInner] using hm
  · exact hnf
  · exact hsink

theorem fixture_statement_root : fixtureStatement.root = TR [fixtureLeaf] := rfl
theorem fixture_statement_domain : fixtureStatement.d = D 1 1 0 := rfl
theorem fixture_statement_outputs :
    fixtureStatement.o1 = SINK 0 ∧ fixtureStatement.o2 = SINK 1 := ⟨rfl, rfl⟩
theorem fixture_statement_amounts :
    fixtureStatement.pub = 1 ∧ fixtureStatement.fee = 1 ∧
    fixtureStatement.rcp = 1 ∧ fixtureStatement.auth = 1 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (2 : F) - 1 = 1
  norm_num

def fixtureShielded : PoolState :=
  { PoolState.init.append [(fixtureLeaf, 2)] with balance := 2 }
def fixturePublished : PoolState :=
  { fixtureShielded with roots := [(sourceId 1 0, 0, (TR [fixtureLeaf]).val)] }
def fixtureReady : PoolState := { fixturePublished with slot := 1 }
def fixtureEvents : List Event := [.shield fixtureInner 2, .publish 0, .tick]

theorem fixture_shield (P : Pool) (h0 : fixtureLeaf ≠ SINK 0)
    (h1 : fixtureLeaf ≠ SINK 1) :
    Step P PoolState.init (.shield fixtureInner 2) fixtureShielded := by
  refine ⟨by decide, by decide, h0, h1, ?_, rfl⟩
  intro _
  decide

theorem fixture_shielded_leaves : fixtureShielded.leaves 0 = [fixtureLeaf] := by
  simp [fixtureShielded, PoolState.append, rollsOver, PoolState.init, CAPACITY, DEPTH]

theorem fixture_shielded_epoch : fixtureShielded.E = 0 := by
  simp [fixtureShielded, PoolState.append, rollsOver, PoolState.init, CAPACITY, DEPTH]

theorem fixture_publish (P : Pool) (ha : P.A = 1) (hr : TR [fixtureLeaf] ≠ 0) :
    Step P fixtureShielded (.publish 0) fixturePublished := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [fixture_shielded_epoch]
  · simp only [fixture_shielded_epoch, ↓reduceIte, fixture_shielded_leaves]
    refine ⟨hr, ?_⟩
    simp [fixturePublished, ha, fixtureShielded, PoolState.append, rollsOver,
      PoolState.init, CAPACITY, DEPTH]

theorem fixture_tick (P : Pool) : Step P fixturePublished .tick fixtureReady := by
  change fixtureReady = { fixturePublished with slot := fixturePublished.slot + 1 }
  simp [fixtureReady, fixturePublished, fixtureShielded, PoolState.append, rollsOver,
    PoolState.init, CAPACITY, DEPTH]

theorem fixture_run (P : Pool) (ha : P.A = 1) (h0 : fixtureLeaf ≠ SINK 0)
    (h1 : fixtureLeaf ≠ SINK 1) (hr : TR [fixtureLeaf] ≠ 0) :
    Run P fixtureEvents fixtureReady := by
  exact Run.snoc (Run.snoc (Run.snoc Run.nil (fixture_shield P h0 h1))
    (fixture_publish P ha hr)) (fixture_tick P)

end
end MSP.NonVacuity
