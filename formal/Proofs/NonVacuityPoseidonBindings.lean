import Proofs.NonVacuityPoseidonBase
import Proofs.NonVacuityFixture
import Proofs.NonVacuityKeccak

namespace MSP.NonVacuity
open PoseidonFixture

theorem fixture_inner_eq : fixtureInner = (9214064348566717547928842125153182075532947154543154780585813679015529804670 : F) := by
  change H2 (H3 1 1 0) 1 = _
  rw [pk1_hash, inner1_hash]

theorem fixture_leaf_eq : fixtureLeaf = (20795034779778091623118163646121075915786898654530388597813261001821138017121 : F) := by
  change H3 2 (H2 (H3 1 1 0) 1) 2 = _
  rw [pk1_hash, inner1_hash, leaf_hash]

theorem fixture_dummy_inner_eq : inner 2 2 = (14268180605625588165168398667097991315372650666397170675907070532013955435053 : F) := by
  change H2 (H3 1 2 0) 2 = _
  rw [pk2_hash, inner2_hash]

theorem fixture_dummy_leaf_eq : cm (inner 2 2) 0 = (7201024204249675916148368033337161003620435898048856910155111105967218025308 : F) := by
  change H3 2 (H2 (H3 1 2 0) 2) 0 = _
  rw [pk2_hash, inner2_hash, dummyLeaf_hash]

theorem fixture_sink0_eq : SINK 0 = (16258033826633421689872739078861374449106838767068609068562777353607448109423 : F) := by
  change H3 2 1 0 = _
  rw [sink0_hash]

theorem fixture_sink1_eq : SINK 1 = (21634092513966667169942431120259753258607452424692259564111922412343817482939 : F) := by
  change H3 2 2 0 = _
  rw [sink1_hash]

theorem fixture_nf1_eq : fixtureStatement.nf1 = (2078667565048261126995952142193965014036398664970972851055714654440913762076 : F) := by
  change H3 4 (H2 (D 1 1 0) 1) (H2 (fixtureLeaf) 0) = _
  rw [domain_one_one_zero_eq, fixture_leaf_eq,
    nfKey1_hash, occurrence1_hash, nf1_hash]

theorem fixture_nf2_eq : fixtureStatement.nf2 = (14733247219625856291985193582540913734334269146722451096619511141630182331973 : F) := by
  change H3 4 (H2 (D 1 1 0) 2) (H2 (cm (inner 2 2) 0) 0) = _
  rw [domain_one_one_zero_eq, fixture_dummy_leaf_eq,
    nfKey2_hash, occurrence2_hash, nf2_hash]

end MSP.NonVacuity
