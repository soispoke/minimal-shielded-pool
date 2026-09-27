import Artifacts.SmallHashGatesLemmas

/-!
# Typed actual small-hash instances

R1CS SHA-256 `e2f6fc89bc0e478231935d7dab10fb07316f2c6dab4303e95da1a390ce84f9bf`.
Inventory SHA-256 `6f90e7cd87fb9a3c473d83f665cefd3392ba6363d1f96eb92baf133a10f09368`.
Generated with `python3 formal/tools/small_hash_gates.py --write`.
Every slice has a kernel-checked membership proof in the full Spend system.
Input/output interface forms are data; their full affine bindings remain separate.
-/

namespace MSP.Artifacts.SmallHashGatesData

open SmallHashGates BetaGates

set_option maxRecDepth 65536

/-- main.spend.note[0].domainKey, constraints 697..936. -/
def slice0 : List Constraint :=
  ([Spend.group2, Spend.group3].flatten.drop 185).take 240

private theorem slice0_mem {c : Constraint} (hc : c ∈ slice0) :
    c ∈ Spend.system.constraints := by
  unfold slice0 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance0 : Instance where
  name := "main.spend.note[0].domainKey"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice0
  constraintCount := rfl
  contains := fun _ hc => slice0_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(5, 1)], [(6, 1)]]
  outputForm := [(791, 1)]

/-- main.spend.note[0].inner, constraints 937..1176. -/
def slice1 : List Constraint :=
  ([Spend.group3, Spend.group4].flatten.drop 169).take 240

private theorem slice1_mem {c : Constraint} (hc : c ∈ slice1) :
    c ∈ Spend.system.constraints := by
  unfold slice1 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance1 : Instance where
  name := "main.spend.note[0].inner"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice1
  constraintCount := rfl
  contains := fun _ hc => slice1_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(1032, 1)], [(8, 1)]]
  outputForm := [(1031, 1)]

/-- main.spend.note[0].leaf, constraints 1177..1434. -/
def slice2 : List Constraint :=
  ([Spend.group4, Spend.group5].flatten.drop 153).take 258

private theorem slice2_mem {c : Constraint} (hc : c ∈ slice2) :
    c ∈ Spend.system.constraints := by
  unfold slice2 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance2 : Instance where
  name := "main.spend.note[0].leaf"
  arity := 3
  partialRounds := 56
  tripleCount := 86
  constraints := slice2
  constraintCount := rfl
  contains := fun _ hc => slice2_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩], ![some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩], ![some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩], ![some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩], ![some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩], ![some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩]]
  partialStage := ![⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
  foldedInput := ![some 0, some 2, none, none]
  inputForms := ![[(0, 2)], [(1031, 1)], [(10, 1)]]
  outputForm := [(770, 1)]

/-- main.spend.note[0].node[0], constraints 1435..1674. -/
def slice3 : List Constraint :=
  ([Spend.group5, Spend.group6].flatten.drop 155).take 240

private theorem slice3_mem {c : Constraint} (hc : c ∈ slice3) :
    c ∈ Spend.system.constraints := by
  unfold slice3 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance3 : Instance where
  name := "main.spend.note[0].node[0]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice3
  constraintCount := rfl
  contains := fun _ hc => slice3_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(730, 1)], [(750, 1)]]
  outputForm := [(771, 1)]

/-- main.spend.note[0].node[1], constraints 1675..1914. -/
def slice4 : List Constraint :=
  ([Spend.group6, Spend.group7].flatten.drop 139).take 240

private theorem slice4_mem {c : Constraint} (hc : c ∈ slice4) :
    c ∈ Spend.system.constraints := by
  unfold slice4 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance4 : Instance where
  name := "main.spend.note[0].node[1]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice4
  constraintCount := rfl
  contains := fun _ hc => slice4_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(731, 1)], [(751, 1)]]
  outputForm := [(772, 1)]

/-- main.spend.note[0].node[2], constraints 1915..2154. -/
def slice5 : List Constraint :=
  ([Spend.group7, Spend.group8].flatten.drop 123).take 240

private theorem slice5_mem {c : Constraint} (hc : c ∈ slice5) :
    c ∈ Spend.system.constraints := by
  unfold slice5 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance5 : Instance where
  name := "main.spend.note[0].node[2]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice5
  constraintCount := rfl
  contains := fun _ hc => slice5_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(732, 1)], [(752, 1)]]
  outputForm := [(773, 1)]

/-- main.spend.note[0].node[3], constraints 2155..2394. -/
def slice6 : List Constraint :=
  ([Spend.group8, Spend.group9].flatten.drop 107).take 240

private theorem slice6_mem {c : Constraint} (hc : c ∈ slice6) :
    c ∈ Spend.system.constraints := by
  unfold slice6 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance6 : Instance where
  name := "main.spend.note[0].node[3]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice6
  constraintCount := rfl
  contains := fun _ hc => slice6_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(733, 1)], [(753, 1)]]
  outputForm := [(774, 1)]

/-- main.spend.note[0].node[4], constraints 2395..2634. -/
def slice7 : List Constraint :=
  ([Spend.group9, Spend.group10].flatten.drop 91).take 240

private theorem slice7_mem {c : Constraint} (hc : c ∈ slice7) :
    c ∈ Spend.system.constraints := by
  unfold slice7 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance7 : Instance where
  name := "main.spend.note[0].node[4]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice7
  constraintCount := rfl
  contains := fun _ hc => slice7_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(734, 1)], [(754, 1)]]
  outputForm := [(775, 1)]

/-- main.spend.note[0].node[5], constraints 2635..2874. -/
def slice8 : List Constraint :=
  ([Spend.group10, Spend.group11].flatten.drop 75).take 240

private theorem slice8_mem {c : Constraint} (hc : c ∈ slice8) :
    c ∈ Spend.system.constraints := by
  unfold slice8 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance8 : Instance where
  name := "main.spend.note[0].node[5]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice8
  constraintCount := rfl
  contains := fun _ hc => slice8_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(735, 1)], [(755, 1)]]
  outputForm := [(776, 1)]

/-- main.spend.note[0].node[6], constraints 2875..3114. -/
def slice9 : List Constraint :=
  ([Spend.group11, Spend.group12].flatten.drop 59).take 240

private theorem slice9_mem {c : Constraint} (hc : c ∈ slice9) :
    c ∈ Spend.system.constraints := by
  unfold slice9 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance9 : Instance where
  name := "main.spend.note[0].node[6]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice9
  constraintCount := rfl
  contains := fun _ hc => slice9_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(736, 1)], [(756, 1)]]
  outputForm := [(777, 1)]

/-- main.spend.note[0].node[7], constraints 3115..3354. -/
def slice10 : List Constraint :=
  ([Spend.group12, Spend.group13].flatten.drop 43).take 240

private theorem slice10_mem {c : Constraint} (hc : c ∈ slice10) :
    c ∈ Spend.system.constraints := by
  unfold slice10 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance10 : Instance where
  name := "main.spend.note[0].node[7]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice10
  constraintCount := rfl
  contains := fun _ hc => slice10_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(737, 1)], [(757, 1)]]
  outputForm := [(778, 1)]

/-- main.spend.note[0].node[8], constraints 3355..3594. -/
def slice11 : List Constraint :=
  ([Spend.group13, Spend.group14].flatten.drop 27).take 240

private theorem slice11_mem {c : Constraint} (hc : c ∈ slice11) :
    c ∈ Spend.system.constraints := by
  unfold slice11 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance11 : Instance where
  name := "main.spend.note[0].node[8]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice11
  constraintCount := rfl
  contains := fun _ hc => slice11_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(738, 1)], [(758, 1)]]
  outputForm := [(779, 1)]

/-- main.spend.note[0].node[9], constraints 3595..3834. -/
def slice12 : List Constraint :=
  ([Spend.group14].flatten.drop 11).take 240

private theorem slice12_mem {c : Constraint} (hc : c ∈ slice12) :
    c ∈ Spend.system.constraints := by
  unfold slice12 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  all_goals simp

def instance12 : Instance where
  name := "main.spend.note[0].node[9]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice12
  constraintCount := rfl
  contains := fun _ hc => slice12_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(739, 1)], [(759, 1)]]
  outputForm := [(780, 1)]

/-- main.spend.note[0].node[10], constraints 3835..4074. -/
def slice13 : List Constraint :=
  ([Spend.group14, Spend.group15].flatten.drop 251).take 240

private theorem slice13_mem {c : Constraint} (hc : c ∈ slice13) :
    c ∈ Spend.system.constraints := by
  unfold slice13 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance13 : Instance where
  name := "main.spend.note[0].node[10]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice13
  constraintCount := rfl
  contains := fun _ hc => slice13_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(740, 1)], [(760, 1)]]
  outputForm := [(781, 1)]

/-- main.spend.note[0].node[11], constraints 4075..4314. -/
def slice14 : List Constraint :=
  ([Spend.group15, Spend.group16].flatten.drop 235).take 240

private theorem slice14_mem {c : Constraint} (hc : c ∈ slice14) :
    c ∈ Spend.system.constraints := by
  unfold slice14 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance14 : Instance where
  name := "main.spend.note[0].node[11]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice14
  constraintCount := rfl
  contains := fun _ hc => slice14_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(741, 1)], [(761, 1)]]
  outputForm := [(782, 1)]

/-- main.spend.note[0].node[12], constraints 4315..4554. -/
def slice15 : List Constraint :=
  ([Spend.group16, Spend.group17].flatten.drop 219).take 240

private theorem slice15_mem {c : Constraint} (hc : c ∈ slice15) :
    c ∈ Spend.system.constraints := by
  unfold slice15 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance15 : Instance where
  name := "main.spend.note[0].node[12]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice15
  constraintCount := rfl
  contains := fun _ hc => slice15_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(742, 1)], [(762, 1)]]
  outputForm := [(783, 1)]

/-- main.spend.note[0].node[13], constraints 4555..4794. -/
def slice16 : List Constraint :=
  ([Spend.group17, Spend.group18].flatten.drop 203).take 240

private theorem slice16_mem {c : Constraint} (hc : c ∈ slice16) :
    c ∈ Spend.system.constraints := by
  unfold slice16 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance16 : Instance where
  name := "main.spend.note[0].node[13]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice16
  constraintCount := rfl
  contains := fun _ hc => slice16_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(743, 1)], [(763, 1)]]
  outputForm := [(784, 1)]

/-- main.spend.note[0].node[14], constraints 4795..5034. -/
def slice17 : List Constraint :=
  ([Spend.group18, Spend.group19].flatten.drop 187).take 240

private theorem slice17_mem {c : Constraint} (hc : c ∈ slice17) :
    c ∈ Spend.system.constraints := by
  unfold slice17 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance17 : Instance where
  name := "main.spend.note[0].node[14]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice17
  constraintCount := rfl
  contains := fun _ hc => slice17_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(744, 1)], [(764, 1)]]
  outputForm := [(785, 1)]

/-- main.spend.note[0].node[15], constraints 5035..5274. -/
def slice18 : List Constraint :=
  ([Spend.group19, Spend.group20].flatten.drop 171).take 240

private theorem slice18_mem {c : Constraint} (hc : c ∈ slice18) :
    c ∈ Spend.system.constraints := by
  unfold slice18 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance18 : Instance where
  name := "main.spend.note[0].node[15]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice18
  constraintCount := rfl
  contains := fun _ hc => slice18_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(745, 1)], [(765, 1)]]
  outputForm := [(786, 1)]

/-- main.spend.note[0].node[16], constraints 5275..5514. -/
def slice19 : List Constraint :=
  ([Spend.group20, Spend.group21].flatten.drop 155).take 240

private theorem slice19_mem {c : Constraint} (hc : c ∈ slice19) :
    c ∈ Spend.system.constraints := by
  unfold slice19 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance19 : Instance where
  name := "main.spend.note[0].node[16]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice19
  constraintCount := rfl
  contains := fun _ hc => slice19_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(746, 1)], [(766, 1)]]
  outputForm := [(787, 1)]

/-- main.spend.note[0].node[17], constraints 5515..5754. -/
def slice20 : List Constraint :=
  ([Spend.group21, Spend.group22].flatten.drop 139).take 240

private theorem slice20_mem {c : Constraint} (hc : c ∈ slice20) :
    c ∈ Spend.system.constraints := by
  unfold slice20 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance20 : Instance where
  name := "main.spend.note[0].node[17]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice20
  constraintCount := rfl
  contains := fun _ hc => slice20_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(747, 1)], [(767, 1)]]
  outputForm := [(788, 1)]

/-- main.spend.note[0].node[18], constraints 5755..5994. -/
def slice21 : List Constraint :=
  ([Spend.group22, Spend.group23].flatten.drop 123).take 240

private theorem slice21_mem {c : Constraint} (hc : c ∈ slice21) :
    c ∈ Spend.system.constraints := by
  unfold slice21 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance21 : Instance where
  name := "main.spend.note[0].node[18]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice21
  constraintCount := rfl
  contains := fun _ hc => slice21_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(748, 1)], [(768, 1)]]
  outputForm := [(789, 1)]

/-- main.spend.note[0].node[19], constraints 5995..6234. -/
def slice22 : List Constraint :=
  ([Spend.group23, Spend.group24].flatten.drop 107).take 240

private theorem slice22_mem {c : Constraint} (hc : c ∈ slice22) :
    c ∈ Spend.system.constraints := by
  unfold slice22 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance22 : Instance where
  name := "main.spend.note[0].node[19]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice22
  constraintCount := rfl
  contains := fun _ hc => slice22_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(749, 1)], [(769, 1)]]
  outputForm := [(790, 1)]

/-- main.spend.note[0].null, constraints 6235..6492. -/
def slice23 : List Constraint :=
  ([Spend.group24, Spend.group25].flatten.drop 91).take 258

private theorem slice23_mem {c : Constraint} (hc : c ∈ slice23) :
    c ∈ Spend.system.constraints := by
  unfold slice23 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance23 : Instance where
  name := "main.spend.note[0].null"
  arity := 3
  partialRounds := 56
  tripleCount := 86
  constraints := slice23
  constraintCount := rfl
  contains := fun _ hc => slice23_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩], ![some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩], ![some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩], ![some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩], ![some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩], ![some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩]]
  partialStage := ![⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
  foldedInput := ![some 0, some 4, none, none]
  inputForms := ![[(0, 4)], [(791, 1)], [(6309, 1)]]
  outputForm := [(99, 1)]

/-- main.spend.note[0].occurrence, constraints 6493..6732. -/
def slice24 : List Constraint :=
  ([Spend.group25, Spend.group26].flatten.drop 93).take 240

private theorem slice24_mem {c : Constraint} (hc : c ∈ slice24) :
    c ∈ Spend.system.constraints := by
  unfold slice24 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance24 : Instance where
  name := "main.spend.note[0].occurrence"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice24
  constraintCount := rfl
  contains := fun _ hc => slice24_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(770, 1)], [(52, 1), (53, 2), (54, 4), (55, 8), (56, 16), (57, 32), (58, 64), (59, 128), (60, 256), (61, 512), (62, 1024), (63, 2048), (64, 4096), (65, 8192), (66, 16384), (67, 32768), (68, 65536), (69, 131072), (70, 262144), (71, 524288)]]
  outputForm := [(6309, 1)]

/-- main.spend.note[0].pk, constraints 6733..6987. -/
def slice25 : List Constraint :=
  ([Spend.group26, Spend.group27].flatten.drop 77).take 255

private theorem slice25_mem {c : Constraint} (hc : c ∈ slice25) :
    c ∈ Spend.system.constraints := by
  unfold slice25 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance25 : Instance where
  name := "main.spend.note[0].pk"
  arity := 3
  partialRounds := 56
  tripleCount := 85
  constraints := slice25
  constraintCount := rfl
  contains := fun _ hc => slice25_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, none], ![some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩], ![some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩], ![some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩], ![some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩], ![some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩]]
  partialStage := ![⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
  foldedInput := ![some 0, some 1, none, some 0]
  inputForms := ![[(0, 1)], [(6, 1)], []]
  outputForm := [(1032, 1)]

/-- main.spend.note[1].domainKey, constraints 7049..7288. -/
def slice26 : List Constraint :=
  ([Spend.group27, Spend.group28].flatten.drop 137).take 240

private theorem slice26_mem {c : Constraint} (hc : c ∈ slice26) :
    c ∈ Spend.system.constraints := by
  unfold slice26 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance26 : Instance where
  name := "main.spend.note[1].domainKey"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice26
  constraintCount := rfl
  contains := fun _ hc => slice26_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(5, 1)], [(7, 1)]]
  outputForm := [(7121, 1)]

/-- main.spend.note[1].inner, constraints 7289..7528. -/
def slice27 : List Constraint :=
  ([Spend.group28, Spend.group29].flatten.drop 121).take 240

private theorem slice27_mem {c : Constraint} (hc : c ∈ slice27) :
    c ∈ Spend.system.constraints := by
  unfold slice27 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance27 : Instance where
  name := "main.spend.note[1].inner"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice27
  constraintCount := rfl
  contains := fun _ hc => slice27_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7362, 1)], [(9, 1)]]
  outputForm := [(7361, 1)]

/-- main.spend.note[1].leaf, constraints 7529..7786. -/
def slice28 : List Constraint :=
  ([Spend.group29, Spend.group30].flatten.drop 105).take 258

private theorem slice28_mem {c : Constraint} (hc : c ∈ slice28) :
    c ∈ Spend.system.constraints := by
  unfold slice28 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance28 : Instance where
  name := "main.spend.note[1].leaf"
  arity := 3
  partialRounds := 56
  tripleCount := 86
  constraints := slice28
  constraintCount := rfl
  contains := fun _ hc => slice28_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩], ![some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩], ![some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩], ![some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩], ![some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩], ![some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩]]
  partialStage := ![⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
  foldedInput := ![some 0, some 2, none, none]
  inputForms := ![[(0, 2)], [(7361, 1)], [(11, 1)]]
  outputForm := [(7100, 1)]

/-- main.spend.note[1].node[0], constraints 7787..8026. -/
def slice29 : List Constraint :=
  ([Spend.group30, Spend.group31].flatten.drop 107).take 240

private theorem slice29_mem {c : Constraint} (hc : c ∈ slice29) :
    c ∈ Spend.system.constraints := by
  unfold slice29 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance29 : Instance where
  name := "main.spend.note[1].node[0]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice29
  constraintCount := rfl
  contains := fun _ hc => slice29_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7060, 1)], [(7080, 1)]]
  outputForm := [(7101, 1)]

/-- main.spend.note[1].node[1], constraints 8027..8266. -/
def slice30 : List Constraint :=
  ([Spend.group31, Spend.group32].flatten.drop 91).take 240

private theorem slice30_mem {c : Constraint} (hc : c ∈ slice30) :
    c ∈ Spend.system.constraints := by
  unfold slice30 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance30 : Instance where
  name := "main.spend.note[1].node[1]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice30
  constraintCount := rfl
  contains := fun _ hc => slice30_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7061, 1)], [(7081, 1)]]
  outputForm := [(7102, 1)]

/-- main.spend.note[1].node[2], constraints 8267..8506. -/
def slice31 : List Constraint :=
  ([Spend.group32, Spend.group33].flatten.drop 75).take 240

private theorem slice31_mem {c : Constraint} (hc : c ∈ slice31) :
    c ∈ Spend.system.constraints := by
  unfold slice31 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance31 : Instance where
  name := "main.spend.note[1].node[2]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice31
  constraintCount := rfl
  contains := fun _ hc => slice31_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7062, 1)], [(7082, 1)]]
  outputForm := [(7103, 1)]

/-- main.spend.note[1].node[3], constraints 8507..8746. -/
def slice32 : List Constraint :=
  ([Spend.group33, Spend.group34].flatten.drop 59).take 240

private theorem slice32_mem {c : Constraint} (hc : c ∈ slice32) :
    c ∈ Spend.system.constraints := by
  unfold slice32 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance32 : Instance where
  name := "main.spend.note[1].node[3]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice32
  constraintCount := rfl
  contains := fun _ hc => slice32_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7063, 1)], [(7083, 1)]]
  outputForm := [(7104, 1)]

/-- main.spend.note[1].node[4], constraints 8747..8986. -/
def slice33 : List Constraint :=
  ([Spend.group34, Spend.group35].flatten.drop 43).take 240

private theorem slice33_mem {c : Constraint} (hc : c ∈ slice33) :
    c ∈ Spend.system.constraints := by
  unfold slice33 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance33 : Instance where
  name := "main.spend.note[1].node[4]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice33
  constraintCount := rfl
  contains := fun _ hc => slice33_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7064, 1)], [(7084, 1)]]
  outputForm := [(7105, 1)]

/-- main.spend.note[1].node[5], constraints 8987..9226. -/
def slice34 : List Constraint :=
  ([Spend.group35, Spend.group36].flatten.drop 27).take 240

private theorem slice34_mem {c : Constraint} (hc : c ∈ slice34) :
    c ∈ Spend.system.constraints := by
  unfold slice34 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance34 : Instance where
  name := "main.spend.note[1].node[5]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice34
  constraintCount := rfl
  contains := fun _ hc => slice34_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7065, 1)], [(7085, 1)]]
  outputForm := [(7106, 1)]

/-- main.spend.note[1].node[6], constraints 9227..9466. -/
def slice35 : List Constraint :=
  ([Spend.group36].flatten.drop 11).take 240

private theorem slice35_mem {c : Constraint} (hc : c ∈ slice35) :
    c ∈ Spend.system.constraints := by
  unfold slice35 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  all_goals simp

def instance35 : Instance where
  name := "main.spend.note[1].node[6]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice35
  constraintCount := rfl
  contains := fun _ hc => slice35_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7066, 1)], [(7086, 1)]]
  outputForm := [(7107, 1)]

/-- main.spend.note[1].node[7], constraints 9467..9706. -/
def slice36 : List Constraint :=
  ([Spend.group36, Spend.group37].flatten.drop 251).take 240

private theorem slice36_mem {c : Constraint} (hc : c ∈ slice36) :
    c ∈ Spend.system.constraints := by
  unfold slice36 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance36 : Instance where
  name := "main.spend.note[1].node[7]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice36
  constraintCount := rfl
  contains := fun _ hc => slice36_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7067, 1)], [(7087, 1)]]
  outputForm := [(7108, 1)]

/-- main.spend.note[1].node[8], constraints 9707..9946. -/
def slice37 : List Constraint :=
  ([Spend.group37, Spend.group38].flatten.drop 235).take 240

private theorem slice37_mem {c : Constraint} (hc : c ∈ slice37) :
    c ∈ Spend.system.constraints := by
  unfold slice37 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance37 : Instance where
  name := "main.spend.note[1].node[8]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice37
  constraintCount := rfl
  contains := fun _ hc => slice37_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7068, 1)], [(7088, 1)]]
  outputForm := [(7109, 1)]

/-- main.spend.note[1].node[9], constraints 9947..10186. -/
def slice38 : List Constraint :=
  ([Spend.group38, Spend.group39].flatten.drop 219).take 240

private theorem slice38_mem {c : Constraint} (hc : c ∈ slice38) :
    c ∈ Spend.system.constraints := by
  unfold slice38 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance38 : Instance where
  name := "main.spend.note[1].node[9]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice38
  constraintCount := rfl
  contains := fun _ hc => slice38_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7069, 1)], [(7089, 1)]]
  outputForm := [(7110, 1)]

/-- main.spend.note[1].node[10], constraints 10187..10426. -/
def slice39 : List Constraint :=
  ([Spend.group39, Spend.group40].flatten.drop 203).take 240

private theorem slice39_mem {c : Constraint} (hc : c ∈ slice39) :
    c ∈ Spend.system.constraints := by
  unfold slice39 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance39 : Instance where
  name := "main.spend.note[1].node[10]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice39
  constraintCount := rfl
  contains := fun _ hc => slice39_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7070, 1)], [(7090, 1)]]
  outputForm := [(7111, 1)]

/-- main.spend.note[1].node[11], constraints 10427..10666. -/
def slice40 : List Constraint :=
  ([Spend.group40, Spend.group41].flatten.drop 187).take 240

private theorem slice40_mem {c : Constraint} (hc : c ∈ slice40) :
    c ∈ Spend.system.constraints := by
  unfold slice40 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance40 : Instance where
  name := "main.spend.note[1].node[11]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice40
  constraintCount := rfl
  contains := fun _ hc => slice40_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7071, 1)], [(7091, 1)]]
  outputForm := [(7112, 1)]

/-- main.spend.note[1].node[12], constraints 10667..10906. -/
def slice41 : List Constraint :=
  ([Spend.group41, Spend.group42].flatten.drop 171).take 240

private theorem slice41_mem {c : Constraint} (hc : c ∈ slice41) :
    c ∈ Spend.system.constraints := by
  unfold slice41 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance41 : Instance where
  name := "main.spend.note[1].node[12]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice41
  constraintCount := rfl
  contains := fun _ hc => slice41_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7072, 1)], [(7092, 1)]]
  outputForm := [(7113, 1)]

/-- main.spend.note[1].node[13], constraints 10907..11146. -/
def slice42 : List Constraint :=
  ([Spend.group42, Spend.group43].flatten.drop 155).take 240

private theorem slice42_mem {c : Constraint} (hc : c ∈ slice42) :
    c ∈ Spend.system.constraints := by
  unfold slice42 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance42 : Instance where
  name := "main.spend.note[1].node[13]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice42
  constraintCount := rfl
  contains := fun _ hc => slice42_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7073, 1)], [(7093, 1)]]
  outputForm := [(7114, 1)]

/-- main.spend.note[1].node[14], constraints 11147..11386. -/
def slice43 : List Constraint :=
  ([Spend.group43, Spend.group44].flatten.drop 139).take 240

private theorem slice43_mem {c : Constraint} (hc : c ∈ slice43) :
    c ∈ Spend.system.constraints := by
  unfold slice43 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance43 : Instance where
  name := "main.spend.note[1].node[14]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice43
  constraintCount := rfl
  contains := fun _ hc => slice43_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7074, 1)], [(7094, 1)]]
  outputForm := [(7115, 1)]

/-- main.spend.note[1].node[15], constraints 11387..11626. -/
def slice44 : List Constraint :=
  ([Spend.group44, Spend.group45].flatten.drop 123).take 240

private theorem slice44_mem {c : Constraint} (hc : c ∈ slice44) :
    c ∈ Spend.system.constraints := by
  unfold slice44 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance44 : Instance where
  name := "main.spend.note[1].node[15]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice44
  constraintCount := rfl
  contains := fun _ hc => slice44_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7075, 1)], [(7095, 1)]]
  outputForm := [(7116, 1)]

/-- main.spend.note[1].node[16], constraints 11627..11866. -/
def slice45 : List Constraint :=
  ([Spend.group45, Spend.group46].flatten.drop 107).take 240

private theorem slice45_mem {c : Constraint} (hc : c ∈ slice45) :
    c ∈ Spend.system.constraints := by
  unfold slice45 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance45 : Instance where
  name := "main.spend.note[1].node[16]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice45
  constraintCount := rfl
  contains := fun _ hc => slice45_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7076, 1)], [(7096, 1)]]
  outputForm := [(7117, 1)]

/-- main.spend.note[1].node[17], constraints 11867..12106. -/
def slice46 : List Constraint :=
  ([Spend.group46, Spend.group47].flatten.drop 91).take 240

private theorem slice46_mem {c : Constraint} (hc : c ∈ slice46) :
    c ∈ Spend.system.constraints := by
  unfold slice46 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance46 : Instance where
  name := "main.spend.note[1].node[17]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice46
  constraintCount := rfl
  contains := fun _ hc => slice46_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7077, 1)], [(7097, 1)]]
  outputForm := [(7118, 1)]

/-- main.spend.note[1].node[18], constraints 12107..12346. -/
def slice47 : List Constraint :=
  ([Spend.group47, Spend.group48].flatten.drop 75).take 240

private theorem slice47_mem {c : Constraint} (hc : c ∈ slice47) :
    c ∈ Spend.system.constraints := by
  unfold slice47 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance47 : Instance where
  name := "main.spend.note[1].node[18]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice47
  constraintCount := rfl
  contains := fun _ hc => slice47_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7078, 1)], [(7098, 1)]]
  outputForm := [(7119, 1)]

/-- main.spend.note[1].node[19], constraints 12347..12586. -/
def slice48 : List Constraint :=
  ([Spend.group48, Spend.group49].flatten.drop 59).take 240

private theorem slice48_mem {c : Constraint} (hc : c ∈ slice48) :
    c ∈ Spend.system.constraints := by
  unfold slice48 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance48 : Instance where
  name := "main.spend.note[1].node[19]"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice48
  constraintCount := rfl
  contains := fun _ hc => slice48_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7079, 1)], [(7099, 1)]]
  outputForm := [(7120, 1)]

/-- main.spend.note[1].null, constraints 12587..12844. -/
def slice49 : List Constraint :=
  ([Spend.group49, Spend.group50].flatten.drop 43).take 258

private theorem slice49_mem {c : Constraint} (hc : c ∈ slice49) :
    c ∈ Spend.system.constraints := by
  unfold slice49 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance49 : Instance where
  name := "main.spend.note[1].null"
  arity := 3
  partialRounds := 56
  tripleCount := 86
  constraints := slice49
  constraintCount := rfl
  contains := fun _ hc => slice49_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩], ![some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩], ![some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩], ![some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩], ![some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩], ![some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩]]
  partialStage := ![⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
  foldedInput := ![some 0, some 4, none, none]
  inputForms := ![[(0, 4)], [(7121, 1)], [(12639, 1)]]
  outputForm := [(100, 1)]

/-- main.spend.note[1].occurrence, constraints 12845..13084. -/
def slice50 : List Constraint :=
  ([Spend.group50, Spend.group51].flatten.drop 45).take 240

private theorem slice50_mem {c : Constraint} (hc : c ∈ slice50) :
    c ∈ Spend.system.constraints := by
  unfold slice50 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance50 : Instance where
  name := "main.spend.note[1].occurrence"
  arity := 2
  partialRounds := 57
  tripleCount := 80
  constraints := slice50
  constraintCount := rfl
  contains := fun _ hc => slice50_mem hc
  fullStage := ![![none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩], ![some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩], ![some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩], ![some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩]]
  partialStage := ![⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
  foldedInput := ![some 0, none, none]
  inputForms := ![[(7100, 1)], [(72, 1), (73, 2), (74, 4), (75, 8), (76, 16), (77, 32), (78, 64), (79, 128), (80, 256), (81, 512), (82, 1024), (83, 2048), (84, 4096), (85, 8192), (86, 16384), (87, 32768), (88, 65536), (89, 131072), (90, 262144), (91, 524288)]]
  outputForm := [(12639, 1)]

/-- main.spend.note[1].pk, constraints 13085..13339. -/
def slice51 : List Constraint :=
  ([Spend.group51, Spend.group52].flatten.drop 29).take 255

private theorem slice51_mem {c : Constraint} (hc : c ∈ slice51) :
    c ∈ Spend.system.constraints := by
  unfold slice51 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance51 : Instance where
  name := "main.spend.note[1].pk"
  arity := 3
  partialRounds := 56
  tripleCount := 85
  constraints := slice51
  constraintCount := rfl
  contains := fun _ hc => slice51_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, none], ![some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩], ![some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩], ![some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩], ![some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩], ![some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩], ![some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩], ![some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩]]
  partialStage := ![⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
  foldedInput := ![some 0, some 1, none, some 0]
  inputForms := ![[(0, 1)], [(7, 1)], []]
  outputForm := [(7362, 1)]

/-- main.spend.outCm[0], constraints 13340..13597. -/
def slice52 : List Constraint :=
  ([Spend.group52, Spend.group53].flatten.drop 28).take 258

private theorem slice52_mem {c : Constraint} (hc : c ∈ slice52) :
    c ∈ Spend.system.constraints := by
  unfold slice52 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance52 : Instance where
  name := "main.spend.outCm[0]"
  arity := 3
  partialRounds := 56
  tripleCount := 86
  constraints := slice52
  constraintCount := rfl
  contains := fun _ hc => slice52_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩], ![some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩], ![some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩], ![some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩], ![some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩], ![some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩]]
  partialStage := ![⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
  foldedInput := ![some 0, some 2, none, none]
  inputForms := ![[(0, 2)], [(92, 1)], [(94, 1)]]
  outputForm := [(101, 1)]

/-- main.spend.outCm[1], constraints 13598..13855. -/
def slice53 : List Constraint :=
  ([Spend.group53, Spend.group54].flatten.drop 30).take 258

private theorem slice53_mem {c : Constraint} (hc : c ∈ slice53) :
    c ∈ Spend.system.constraints := by
  unfold slice53 at hc
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp
    (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  apply List.mem_flatten.mpr
  refine ⟨group, ?_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

def instance53 : Instance where
  name := "main.spend.outCm[1]"
  arity := 3
  partialRounds := 56
  tripleCount := 86
  constraints := slice53
  constraintCount := rfl
  contains := fun _ hc => slice53_mem hc
  fullStage := ![![none, none, some ⟨0, by decide⟩, some ⟨1, by decide⟩], ![some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩], ![some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩], ![some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩], ![some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩], ![some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩], ![some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩], ![some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩]]
  partialStage := ![⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
  foldedInput := ![some 0, some 2, none, none]
  inputForms := ![[(0, 2)], [(93, 1)], [(95, 1)]]
  outputForm := [(102, 1)]

def instances : Vector Instance 54 :=
  ⟨#[instance0, instance1, instance2, instance3, instance4, instance5, instance6, instance7, instance8, instance9, instance10, instance11, instance12, instance13, instance14, instance15, instance16, instance17, instance18, instance19, instance20, instance21, instance22, instance23, instance24, instance25, instance26, instance27, instance28, instance29, instance30, instance31, instance32, instance33, instance34, instance35, instance36, instance37, instance38, instance39, instance40, instance41, instance42, instance43, instance44, instance45, instance46, instance47, instance48, instance49, instance50, instance51, instance52, instance53], rfl⟩

def gate (i : Fin 54) : Instance := instances.get i

end MSP.Artifacts.SmallHashGatesData
