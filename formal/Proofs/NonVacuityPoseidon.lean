import Proofs.NonVacuityPoseidonPaths

namespace MSP.NonVacuity

theorem fixture_leaf_ne_sink0 : fixtureLeaf ≠ SINK 0 := by
  rw [fixture_leaf_eq, fixture_sink0_eq]
  decide

theorem fixture_leaf_ne_sink1 : fixtureLeaf ≠ SINK 1 := by
  rw [fixture_leaf_eq, fixture_sink1_eq]
  decide

theorem fixture_root_ne_zero : TR [fixtureLeaf] ≠ 0 := by
  rw [fixture_root_eq]
  decide

theorem fixture_nullifiers_distinct : fixtureStatement.nf1 ≠ fixtureStatement.nf2 := by
  rw [fixture_nf1_eq, fixture_nf2_eq]
  decide

theorem fixture_sinks_distinct : SINK 0 ≠ SINK 1 := by
  rw [fixture_sink0_eq, fixture_sink1_eq]
  decide

theorem fixture_nf1_ne_zero : fixtureStatement.nf1 ≠ 0 := by
  rw [fixture_nf1_eq]
  decide

theorem fixture_nf2_ne_zero : fixtureStatement.nf2 ≠ 0 := by
  rw [fixture_nf2_eq]
  decide

end MSP.NonVacuity
