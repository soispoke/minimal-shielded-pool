import Proofs.NonVacuityFixtureRun
import Proofs.NonVacuityEncoding

namespace MSP.NonVacuity

noncomputable section

/-- W1's ideal verifier ignores proof bytes, but A6 still checks all eight
coordinate words and rejects point-at-infinity encodings. -/
def fixtureProof : List UInt8 := (List.replicate 8 1).flatMap u256

theorem fixtureProof_length : fixtureProof.length = 256 := by
  rw [fixtureProof, u256_flatMap_length, List.length_replicate]

theorem fixtureProof_word (j : ℕ) (hj : j < 8) : wordAt fixtureProof (32 * j) = 1 := by
  have hi : j < (List.replicate 8 (1 : ℕ)).length := by simpa using hj
  have hn : (List.replicate 8 (1 : ℕ))[j] < 2 ^ 256 := by
    simpa only [List.getElem_replicate] using (show (1 : ℕ) < 2 ^ 256 by decide)
  simpa only [List.append_nil, fixtureProof, List.getElem_replicate] using
    wordAt_words (List.replicate 8 1) [] j hi hn

theorem fixtureProof_bounds : ∀ j < 8, wordAt fixtureProof (32 * j) < q := by
  intro j hj
  rw [fixtureProof_word j hj]
  decide

theorem fixtureProof_nonInfinity : PointsNotInfinity fixtureProof := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩
  · simpa using (show wordAt fixtureProof (32 * 0) ≠ 0 by
      rw [fixtureProof_word 0 (by decide)]; decide)
  · simpa using (show wordAt fixtureProof (32 * 2) ≠ 0 by
      rw [fixtureProof_word 2 (by decide)]; decide)
  · simpa using (show wordAt fixtureProof (32 * 6) ≠ 0 by
      rw [fixtureProof_word 6 (by decide)]; decide)

theorem fixtureData_bounds : ∀ n ∈ settlementWords fixtureData, n < 2 ^ 256 := by
  intro n hn
  have hp : p < 2 ^ 256 := by decide
  have hr := lt_trans (ZMod.val_lt fixtureStatement.root) hp
  have hd := lt_trans (ZMod.val_lt fixtureStatement.d) hp
  have hn1 := lt_trans (ZMod.val_lt fixtureStatement.nf1) hp
  have hn2 := lt_trans (ZMod.val_lt fixtureStatement.nf2) hp
  have ho1 := lt_trans (ZMod.val_lt (SINK 0)) hp
  have ho2 := lt_trans (ZMod.val_lt (SINK 1)) hp
  simp only [settlementWords, fixtureData, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | assumption | decide

def fixtureTx : FrameTx := encodeTx 1 1 fixtureData fixtureProof (β fixtureStatement) 1

theorem fixtureTx_data : settleData fixtureTx = fixtureData :=
  encodeTx_settleData 1 1 fixtureData fixtureProof (β fixtureStatement) 1 fixtureData_bounds

theorem fixtureTx_keys : fixtureTx.nonceKeys = fixtureKeys := rfl
theorem fixtureTx_cost : fixtureTx.maxCost = 1 := rfl
theorem fixtureTx_proof : proofOf fixtureTx = fixtureProof :=
  encodeTx_proofOf 1 1 fixtureData fixtureProof (β fixtureStatement) 1 fixtureProof_length

theorem fixtureTx_publics : verifiedPublics fixtureTx =
    (β fixtureStatement, γ fixtureStatement (α fixtureStatement + β fixtureStatement),
      α fixtureStatement) := by
  rw [fixtureTx, encodeTx_verifiedPublics _ _ _ _ _ _ fixtureProof_length fixtureData_bounds,
    fixtureData_statement]

theorem fixtureData_checks (hn1 : fixtureStatement.nf1 ≠ 0)
    (hn2 : fixtureStatement.nf2 ≠ 0) : dataChecks 1 1 fixtureData := by
  have hn1v : fixtureStatement.nf1.val ≠ 0 := by
    intro hz
    exact hn1 ((ZMod.val_eq_zero _).mp hz)
  have hn2v : fixtureStatement.nf2.val ≠ 0 := by
    intro hz
    exact hn2 ((ZMod.val_eq_zero _).mp hz)
  unfold dataChecks
  dsimp only [fixtureData]
  exact ⟨hn1v, hn2v, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
    ZMod.val_lt _, ZMod.val_lt _, by decide, by decide, by decide, by decide,
    by decide, by decide, rfl⟩

theorem fixtureTx_accepted (a : Assignment) (ha : Satisfied a)
    (hp : publicOf a = (β fixtureStatement,
      γ fixtureStatement (α fixtureStatement + β fixtureStatement), α fixtureStatement))
    (hn1 : fixtureStatement.nf1 ≠ 0) (hn2 : fixtureStatement.nf2 ≠ 0) :
    Acc 1 1 (idealPool 1 1 a).verifies 1 fixtureTx := by
  apply encodeTx_Acc 1 1 fixtureData fixtureProof (β fixtureStatement) 1 _
    fixtureData_bounds fixtureProof_length (by decide) (by decide)
    (fixtureData_checks hn1 hn2) fixtureProof_bounds fixtureProof_nonInfinity
  · rw [fixtureData_statement]
    exact ⟨a, ha, hp⟩
  · decide

end
end MSP.NonVacuity
