import Proofs.NonVacuityPoseidonBindings
import Proofs.NonVacuityPoseidonNodes0
import Proofs.NonVacuityPoseidonNodes1
import Proofs.NonVacuityPoseidonZeros

namespace MSP.NonVacuity
open PoseidonFixture

private theorem singleton_root_step (h : ℕ) (leaf : F) :
    treeRoot (h + 1) [leaf] = H2 (treeRoot h [leaf]) (Z h) := by
  have hp : 0 < 2 ^ h := by positivity
  have ht : ([leaf] : List F).take (2 ^ h) = [leaf] := by
    apply List.take_of_length_le
    change 1 ≤ 2 ^ h
    omega
  have hd : ([leaf] : List F).drop (2 ^ h) = [] := by
    apply List.drop_eq_nil_of_le
    change 1 ≤ 2 ^ h
    omega
  simp only [treeRoot, ht, hd, treeRoot_nil]

private theorem real_value_0 : treeRoot 0 [fixtureLeaf] = (20795034779778091623118163646121075915786898654530388597813261001821138017121 : F) := fixture_leaf_eq

private theorem real_value_1 : treeRoot 1 [fixtureLeaf] = (15434416286114236240925902910231384388267306813979825311824820727015681580983 : F) := by
  rw [singleton_root_step 0, real_value_0, zero_value ⟨0, by decide⟩]
  exact real0_hash

private theorem real_value_2 : treeRoot 2 [fixtureLeaf] = (18366163375229454574390794171087182643217697484069095416572779668075283224617 : F) := by
  rw [singleton_root_step 1, real_value_1, zero_value ⟨1, by decide⟩]
  exact real1_hash

private theorem real_value_3 : treeRoot 3 [fixtureLeaf] = (1028542350002788764768208451860718152148347388524411211841108723200743781035 : F) := by
  rw [singleton_root_step 2, real_value_2, zero_value ⟨2, by decide⟩]
  exact real2_hash

private theorem real_value_4 : treeRoot 4 [fixtureLeaf] = (1959883460505034632234354001277586490223410827060376400665093604226576521756 : F) := by
  rw [singleton_root_step 3, real_value_3, zero_value ⟨3, by decide⟩]
  exact real3_hash

private theorem real_value_5 : treeRoot 5 [fixtureLeaf] = (16298700082168551989319290237824077887277655742864281576494598367683933526628 : F) := by
  rw [singleton_root_step 4, real_value_4, zero_value ⟨4, by decide⟩]
  exact real4_hash

private theorem real_value_6 : treeRoot 6 [fixtureLeaf] = (14691515919918979763991719590041198288416323937042949623652241526725118056900 : F) := by
  rw [singleton_root_step 5, real_value_5, zero_value ⟨5, by decide⟩]
  exact real5_hash

private theorem real_value_7 : treeRoot 7 [fixtureLeaf] = (6938437955372967949482335766028452484103943810183461690373612509797762573100 : F) := by
  rw [singleton_root_step 6, real_value_6, zero_value ⟨6, by decide⟩]
  exact real6_hash

private theorem real_value_8 : treeRoot 8 [fixtureLeaf] = (3438880150159457128517828827605721722176847993524107357252226579521847183966 : F) := by
  rw [singleton_root_step 7, real_value_7, zero_value ⟨7, by decide⟩]
  exact real7_hash

private theorem real_value_9 : treeRoot 9 [fixtureLeaf] = (16689791434915733746948366569107521091238232190159107266717672991786862590233 : F) := by
  rw [singleton_root_step 8, real_value_8, zero_value ⟨8, by decide⟩]
  exact real8_hash

private theorem real_value_10 : treeRoot 10 [fixtureLeaf] = (1245048999273990486926475576101474852612238295267658887855667614327208201473 : F) := by
  rw [singleton_root_step 9, real_value_9, zero_value ⟨9, by decide⟩]
  exact real9_hash

private theorem real_value_11 : treeRoot 11 [fixtureLeaf] = (11519110035985208294317110484389933902358886308470481826876361456455474529345 : F) := by
  rw [singleton_root_step 10, real_value_10, zero_value ⟨10, by decide⟩]
  exact real10_hash

private theorem real_value_12 : treeRoot 12 [fixtureLeaf] = (21224896077531002093699203794027191167231293396202942914786555061108764903363 : F) := by
  rw [singleton_root_step 11, real_value_11, zero_value ⟨11, by decide⟩]
  exact real11_hash

private theorem real_value_13 : treeRoot 13 [fixtureLeaf] = (2904527874774217178927237627253437969528212662887965190518668801937742197876 : F) := by
  rw [singleton_root_step 12, real_value_12, zero_value ⟨12, by decide⟩]
  exact real12_hash

private theorem real_value_14 : treeRoot 14 [fixtureLeaf] = (19394752908604218020487193535839478038517486376266766361306122047694355604939 : F) := by
  rw [singleton_root_step 13, real_value_13, zero_value ⟨13, by decide⟩]
  exact real13_hash

private theorem real_value_15 : treeRoot 15 [fixtureLeaf] = (19048176236728787329212879462523887235127645846085185452432443039047065593186 : F) := by
  rw [singleton_root_step 14, real_value_14, zero_value ⟨14, by decide⟩]
  exact real14_hash

private theorem real_value_16 : treeRoot 16 [fixtureLeaf] = (8062584409710906536992548126452149828531041707677471330729391369568215830369 : F) := by
  rw [singleton_root_step 15, real_value_15, zero_value ⟨15, by decide⟩]
  exact real15_hash

private theorem real_value_17 : treeRoot 17 [fixtureLeaf] = (20170588142907252758360001651923756866789561903399796120501583697236482122446 : F) := by
  rw [singleton_root_step 16, real_value_16, zero_value ⟨16, by decide⟩]
  exact real16_hash

private theorem real_value_18 : treeRoot 18 [fixtureLeaf] = (20498488265274331862343713136135947197805481541328910976767160629111214666370 : F) := by
  rw [singleton_root_step 17, real_value_17, zero_value ⟨17, by decide⟩]
  exact real17_hash

private theorem real_value_19 : treeRoot 19 [fixtureLeaf] = (7547529925826795688310191407815580292687076033491013295037202210842070701334 : F) := by
  rw [singleton_root_step 18, real_value_18, zero_value ⟨18, by decide⟩]
  exact real18_hash

private theorem real_value_20 : treeRoot 20 [fixtureLeaf] = (4672675675891064292615413573032888530994442186079076763921881607647678868115 : F) := by
  rw [singleton_root_step 19, real_value_19, zero_value ⟨19, by decide⟩]
  exact real19_hash

theorem real_value (i : Fin 21) : treeRoot i.val [fixtureLeaf] = realValues i := by
  fin_cases i
  · exact real_value_0
  · exact real_value_1
  · exact real_value_2
  · exact real_value_3
  · exact real_value_4
  · exact real_value_5
  · exact real_value_6
  · exact real_value_7
  · exact real_value_8
  · exact real_value_9
  · exact real_value_10
  · exact real_value_11
  · exact real_value_12
  · exact real_value_13
  · exact real_value_14
  · exact real_value_15
  · exact real_value_16
  · exact real_value_17
  · exact real_value_18
  · exact real_value_19
  · exact real_value_20

theorem fixture_root_eq : TR [fixtureLeaf] = (4672675675891064292615413573032888530994442186079076763921881607647678868115 : F) := real_value_20

theorem fixture_statement_root_eq : fixtureStatement.root = (4672675675891064292615413573032888530994442186079076763921881607647678868115 : F) :=
  fixture_statement_root.trans fixture_root_eq

end MSP.NonVacuity
