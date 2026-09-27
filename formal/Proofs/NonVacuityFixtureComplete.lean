import Proofs.NonVacuityFixtureEncoding
import Proofs.NonVacuityFixtureQueries

/-! Assembly of the concrete model witness from its finite numeric
certificates. The conditions below must all be discharged by concrete hash
evaluation before obtaining the unqualified W1 theorem. -/

namespace MSP.NonVacuity

noncomputable section

theorem fixture_w1_of_certificates (table : List (Query × ℕ))
    (hcover : ∀ q ∈ fixtureQueries, ∃ n, (q, n) ∈ table)
    (hvalue : ∀ q n, (q, n) ∈ table → queryValue q = n)
    (hunique : TableUnique table)
    (hlarge : ∀ q n, (q, n) ∈ table → 2 ^ 64 ≤ n)
    (hleaf0 : fixtureLeaf ≠ SINK 0) (hleaf1 : fixtureLeaf ≠ SINK 1)
    (hroot : TR [fixtureLeaf] ≠ 0)
    (hnf : fixtureStatement.nf1 ≠ fixtureStatement.nf2)
    (hsink : SINK 0 ≠ SINK 1)
    (hn1 : fixtureStatement.nf1 ≠ 0) (hn2 : fixtureStatement.nf2 ≠ 0) : W1 := by
  obtain ⟨a, ha, hx, hw, hp⟩ :=
    c1c fixtureStatement fixtureWitness (α fixtureStatement) (fixture_relation hnf hsink)
  have hpub : verifiedPublics fixtureTx = publicOf a := fixtureTx_publics.trans hp.symm
  have hpre := fixture_settlePre (idealPool 1 1 a) rfl rfl hn1 hn2 hsink
  refine ⟨idealPool 1 1 a, fixtureEvents, fixtureReady, fixtureTx, 1, fixtureSettled,
    idealPool_ideal 1 1 a ha, ?_, fixture_run _ rfl hleaf0 hleaf1 hroot, ?_, ?_, ?_⟩
  · exact idealPool_exact 1 1 a
  · exact fixture_spend a fixtureTx fixtureTx_data fixtureTx_keys fixtureTx_cost hpub hw
      (fixtureTx_accepted a ha hp hn1 hn2) hnf hpre
  · simpa only [fixtureTx_data] using hpre
  · apply no_badEvent_of_table _ _ _ table
    · simpa only [fixture_queries_eq a fixtureTx fixtureTx_data fixtureTx_keys hpub hx hw]
        using hcover
    · exact hvalue
    · exact hunique
    · exact hlarge
    · apply fixture_no_compression_break 1 1 a fixtureTx 1 hpub
      rw [fixtureTx_data, fixtureData_statement]
      exact hx
    · exact fixture_no_extraction_failure 1 1 a ha fixtureTx 1 hpub

end
end MSP.NonVacuity
