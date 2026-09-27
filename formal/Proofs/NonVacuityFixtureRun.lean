import Proofs.NonVacuityFixture

/-! State-machine checks for the fixed W1 candidate. The transaction encoding
and concrete finite hash certificates are supplied by separate modules. -/

namespace MSP.NonVacuity

noncomputable section

def fixtureData : SettleData :=
  ⟨fixtureStatement.root.val, 0, 0, fixtureStatement.d.val,
   fixtureStatement.nf1.val, fixtureStatement.nf2.val,
   (SINK 0).val, (SINK 1).val, 1, 1, 1, 1⟩

theorem fixtureData_statement : fixtureData.stmt = fixtureStatement := by
  obtain ⟨hp, hf, hr, ha⟩ := fixture_statement_amounts
  obtain ⟨ho1, ho2⟩ := fixture_statement_outputs
  cases he : fixtureStatement
  simp only [SettleData.stmt, fixtureData, he] at *
  simp only [ZMod.natCast_zmod_val, hp, hf, hr, ha, ho1, ho2, Nat.cast_one]

theorem fixture_ready_epoch : fixtureReady.E = 0 := fixture_shielded_epoch

theorem fixture_ready_credit : fixtureReady.credit = 0 := by
  simp [fixtureReady, fixturePublished, fixtureShielded, PoolState.append, rollsOver,
    PoolState.init, CAPACITY, DEPTH]

theorem fixture_settlePre (P : Pool) (hA : P.A = 1) (hc : P.c = 1)
    (hn1 : fixtureStatement.nf1 ≠ 0) (hn2 : fixtureStatement.nf2 ≠ 0)
    (hsink : SINK 0 ≠ SINK 1) : SettlePre fixtureReady P fixtureData := by
  have hn1v : fixtureStatement.nf1.val ≠ 0 := by
    intro hz
    exact hn1 ((ZMod.val_eq_zero _).mp hz)
  have hn2v : fixtureStatement.nf2.val ≠ 0 := by
    intro hz
    exact hn2 ((ZMod.val_eq_zero _).mp hz)
  have hsv : (SINK 0).val ≠ (SINK 1).val := by
    intro he
    exact hsink (ZMod.val_injective p he)
  unfold SettlePre
  dsimp only [fixtureData]
  refine ⟨by decide, by decide, by decide, hn1v, hn2v, by decide, ?_, ?_,
    ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
    ZMod.val_lt _, ZMod.val_lt _, by decide, by decide, by decide,
    hsv, hsv, Ne.symm hsv, ?_, ?_⟩
  · rw [fixture_statement_domain, hA, hc]
  · rw [fixture_ready_epoch]
  · intro _
    rw [fixture_ready_epoch]
    decide
  · intro _
    rw [fixture_ready_credit]
    decide

def fixtureKeys : List ℕ :=
  [min fixtureData.nf1 fixtureData.nf2, max fixtureData.nf1 fixtureData.nf2]

theorem fixture_keys_pairwise (hn : fixtureStatement.nf1 ≠ fixtureStatement.nf2) :
    fixtureKeys.Pairwise (· < ·) := by
  have hv : fixtureStatement.nf1.val ≠ fixtureStatement.nf2.val := by
    intro he
    exact hn (ZMod.val_injective p he)
  simpa [fixtureKeys, fixtureData] using hv

theorem fixture_keys_bounded : ∀ k ∈ fixtureKeys, k < 2 ^ 256 := by
  intro k hk
  have hp : p < 2 ^ 256 := by decide
  have h1 := ZMod.val_lt fixtureStatement.nf1
  have h2 := ZMod.val_lt fixtureStatement.nf2
  simp only [fixtureKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  dsimp only [fixtureData] at hk
  rcases hk with rfl | rfl <;> omega

def fixtureSettled : PoolState :=
  { fixtureReady with
    keys := fixtureKeys
    spent := [⟨0, 0⟩]
    balance := 1
    credit := Finsupp.single 1 1
    credited := Finsupp.single 1 1 }

theorem fixture_newLeaves : newLeaves fixtureData fixtureWitness = [] := by
  simp only [newLeaves, fixtureData, ↓reduceIte, List.append_nil]

theorem fixture_inputs : inputsOf fixtureData fixtureWitness = [⟨0, 0⟩] := by
  have htwo : (2 : F) ≠ 0 := by decide
  simp [inputsOf, fixtureData, fixtureWitness, fixtureSpend, mkSpend, List.finRange,
    List.ofFn_succ, htwo]

theorem append_nil (s : PoolState) : s.append [] = s := by
  simp [PoolState.append, rollsOver]

theorem fixture_ready_roots :
    fixtureReady.roots = [(sourceId 1 0, 0, fixtureStatement.root.val)] := rfl

theorem fixture_ready_keys : fixtureReady.keys = [] := by
  simp [fixtureReady, fixturePublished, fixtureShielded, PoolState.append, rollsOver,
    PoolState.init, CAPACITY, DEPTH]

theorem fixture_ready_balance : fixtureReady.balance = 2 := rfl
theorem fixture_ready_slot : fixtureReady.slot = 1 := rfl

theorem fixture_spend (a : Assignment) (tx : FrameTx)
    (hsd : settleData tx = fixtureData)
    (hkeys : tx.nonceKeys = fixtureKeys) (hcost : tx.maxCost = 1)
    (hpub : verifiedPublics tx = publicOf a) (hwit : witOf a = fixtureWitness)
    (hacc : Acc 1 1 (idealPool 1 1 a).verifies 1 tx)
    (hn : fixtureStatement.nf1 ≠ fixtureStatement.nf2)
    (hpre : SettlePre fixtureReady (idealPool 1 1 a) fixtureData) :
    Step (idealPool 1 1 a) fixtureReady (.spend tx 1) fixtureSettled := by
  change Acc _ _ _ _ _ ∧ _
  refine ⟨hacc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hkeys] using fixture_keys_bounded
  · simpa only [hkeys] using fixture_keys_pairwise hn
  · simp [fixture_ready_keys]
  · simp [hsd, fixtureData, idealPool, fixture_ready_roots, lastWrite, fixture_ready_slot]
  · rw [hcost, fixture_ready_balance]
    decide
  · rw [hcost]
  · simp only [hsd, hpre, ↓reduceIte, extOf, hpub, idealPool_preferred,
      hwit, fixture_newLeaves, append_nil, fixture_inputs, hkeys]
    simp [fixtureSettled, fixtureData, fixtureReady, fixturePublished, fixtureShielded,
      PoolState.append, rollsOver, PoolState.init, CAPACITY, DEPTH]

end
end MSP.NonVacuity
