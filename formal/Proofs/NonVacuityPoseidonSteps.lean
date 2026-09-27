import Proofs.NonVacuityPoseidonNodes0
import Proofs.NonVacuityPoseidonNodes1
import Proofs.NonVacuityPoseidonNodes2
import Proofs.NonVacuityPoseidonNodes3
import Proofs.NonVacuityPoseidonZeros

namespace MSP.NonVacuity.PoseidonFixture

theorem zero_step (i : Fin 20) :
    H2 (zeroValues i.castSucc) (zeroValues i.castSucc) = zeroValues i.succ := by
  fin_cases i
  · exact zero0_hash
  · exact zero1_hash
  · exact zero2_hash
  · exact zero3_hash
  · exact zero4_hash
  · exact zero5_hash
  · exact zero6_hash
  · exact zero7_hash
  · exact zero8_hash
  · exact zero9_hash
  · exact zero10_hash
  · exact zero11_hash
  · exact zero12_hash
  · exact zero13_hash
  · exact zero14_hash
  · exact zero15_hash
  · exact zero16_hash
  · exact zero17_hash
  · exact zero18_hash
  · exact zero19_hash

theorem real_step (i : Fin 20) :
    H2 (realValues i.castSucc) (zeroValues i.castSucc) = realValues i.succ := by
  fin_cases i
  · exact real0_hash
  · exact real1_hash
  · exact real2_hash
  · exact real3_hash
  · exact real4_hash
  · exact real5_hash
  · exact real6_hash
  · exact real7_hash
  · exact real8_hash
  · exact real9_hash
  · exact real10_hash
  · exact real11_hash
  · exact real12_hash
  · exact real13_hash
  · exact real14_hash
  · exact real15_hash
  · exact real16_hash
  · exact real17_hash
  · exact real18_hash
  · exact real19_hash

theorem dummy_step (i : Fin 20) :
    H2 (dummyValues i.castSucc) 0 = dummyValues i.succ := by
  fin_cases i
  · exact dummy0_hash
  · exact dummy1_hash
  · exact dummy2_hash
  · exact dummy3_hash
  · exact dummy4_hash
  · exact dummy5_hash
  · exact dummy6_hash
  · exact dummy7_hash
  · exact dummy8_hash
  · exact dummy9_hash
  · exact dummy10_hash
  · exact dummy11_hash
  · exact dummy12_hash
  · exact dummy13_hash
  · exact dummy14_hash
  · exact dummy15_hash
  · exact dummy16_hash
  · exact dummy17_hash
  · exact dummy18_hash
  · exact dummy19_hash

end MSP.NonVacuity.PoseidonFixture
