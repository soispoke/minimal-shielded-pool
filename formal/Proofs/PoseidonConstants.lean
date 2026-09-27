import Poseidon.Hash
import Spec.Tree
import Mathlib.Tactic.FinCases

/-! Kernel-checked equalities for all 20 zero-hash steps and the resulting
C6 constants. Each step uses ordinary `decide`; chain lemmas reuse its proof
instead of re-evaluating the entire recursive zero tree. The remaining C6
tree invariant and concrete specification binding are separate obligations. -/

namespace MSP

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem poseidon_zero_step_0 :
    Poseidon.hash2 (0 : F) (0 : F) =
      (0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864 : F) := by
  decide

private theorem poseidon_zero_step_1 :
    Poseidon.hash2 (0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864 : F) (0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864 : F) =
      (0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1 : F) := by
  decide

private theorem poseidon_zero_step_2 :
    Poseidon.hash2 (0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1 : F) (0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1 : F) =
      (0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238 : F) := by
  decide

private theorem poseidon_zero_step_3 :
    Poseidon.hash2 (0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238 : F) (0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238 : F) =
      (0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a : F) := by
  decide

private theorem poseidon_zero_step_4 :
    Poseidon.hash2 (0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a : F) (0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a : F) =
      (0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55 : F) := by
  decide

private theorem poseidon_zero_step_5 :
    Poseidon.hash2 (0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55 : F) (0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55 : F) =
      (0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78 : F) := by
  decide

private theorem poseidon_zero_step_6 :
    Poseidon.hash2 (0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78 : F) (0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78 : F) =
      (0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d : F) := by
  decide

private theorem poseidon_zero_step_7 :
    Poseidon.hash2 (0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d : F) (0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d : F) =
      (0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61 : F) := by
  decide

private theorem poseidon_zero_step_8 :
    Poseidon.hash2 (0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61 : F) (0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61 : F) =
      (0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747 : F) := by
  decide

private theorem poseidon_zero_step_9 :
    Poseidon.hash2 (0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747 : F) (0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747 : F) =
      (0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2 : F) := by
  decide

private theorem poseidon_zero_step_10 :
    Poseidon.hash2 (0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2 : F) (0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2 : F) =
      (0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636 : F) := by
  decide

private theorem poseidon_zero_step_11 :
    Poseidon.hash2 (0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636 : F) (0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636 : F) =
      (0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a : F) := by
  decide

private theorem poseidon_zero_step_12 :
    Poseidon.hash2 (0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a : F) (0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a : F) =
      (0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0 : F) := by
  decide

private theorem poseidon_zero_step_13 :
    Poseidon.hash2 (0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0 : F) (0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0 : F) =
      (0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c : F) := by
  decide

private theorem poseidon_zero_step_14 :
    Poseidon.hash2 (0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c : F) (0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c : F) =
      (0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92 : F) := by
  decide

private theorem poseidon_zero_step_15 :
    Poseidon.hash2 (0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92 : F) (0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92 : F) =
      (0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323 : F) := by
  decide

private theorem poseidon_zero_step_16 :
    Poseidon.hash2 (0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323 : F) (0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323 : F) =
      (0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992 : F) := by
  decide

private theorem poseidon_zero_step_17 :
    Poseidon.hash2 (0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992 : F) (0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992 : F) =
      (0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f : F) := by
  decide

private theorem poseidon_zero_step_18 :
    Poseidon.hash2 (0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f : F) (0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f : F) =
      (0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca : F) := by
  decide

private theorem poseidon_zero_step_19 :
    Poseidon.hash2 (0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca : F) (0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca : F) =
      (0x2134e76ac5d21aab186c2be1dd8f84ee880a1e46eaf712f9d371b6df22191f3e : F) := by
  decide

private theorem poseidon_zero_value_0 : Poseidon.zeroHash 0 = (0 : F) := rfl

private theorem poseidon_zero_value_1 :
    Poseidon.zeroHash 1 = (0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 0) (Poseidon.zeroHash 0) = _
  rw [poseidon_zero_value_0]
  exact poseidon_zero_step_0

private theorem poseidon_zero_value_2 :
    Poseidon.zeroHash 2 = (0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 1) (Poseidon.zeroHash 1) = _
  rw [poseidon_zero_value_1]
  exact poseidon_zero_step_1

private theorem poseidon_zero_value_3 :
    Poseidon.zeroHash 3 = (0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 2) (Poseidon.zeroHash 2) = _
  rw [poseidon_zero_value_2]
  exact poseidon_zero_step_2

private theorem poseidon_zero_value_4 :
    Poseidon.zeroHash 4 = (0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 3) (Poseidon.zeroHash 3) = _
  rw [poseidon_zero_value_3]
  exact poseidon_zero_step_3

private theorem poseidon_zero_value_5 :
    Poseidon.zeroHash 5 = (0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 4) (Poseidon.zeroHash 4) = _
  rw [poseidon_zero_value_4]
  exact poseidon_zero_step_4

private theorem poseidon_zero_value_6 :
    Poseidon.zeroHash 6 = (0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 5) (Poseidon.zeroHash 5) = _
  rw [poseidon_zero_value_5]
  exact poseidon_zero_step_5

private theorem poseidon_zero_value_7 :
    Poseidon.zeroHash 7 = (0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 6) (Poseidon.zeroHash 6) = _
  rw [poseidon_zero_value_6]
  exact poseidon_zero_step_6

private theorem poseidon_zero_value_8 :
    Poseidon.zeroHash 8 = (0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 7) (Poseidon.zeroHash 7) = _
  rw [poseidon_zero_value_7]
  exact poseidon_zero_step_7

private theorem poseidon_zero_value_9 :
    Poseidon.zeroHash 9 = (0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 8) (Poseidon.zeroHash 8) = _
  rw [poseidon_zero_value_8]
  exact poseidon_zero_step_8

private theorem poseidon_zero_value_10 :
    Poseidon.zeroHash 10 = (0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 9) (Poseidon.zeroHash 9) = _
  rw [poseidon_zero_value_9]
  exact poseidon_zero_step_9

private theorem poseidon_zero_value_11 :
    Poseidon.zeroHash 11 = (0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 10) (Poseidon.zeroHash 10) = _
  rw [poseidon_zero_value_10]
  exact poseidon_zero_step_10

private theorem poseidon_zero_value_12 :
    Poseidon.zeroHash 12 = (0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 11) (Poseidon.zeroHash 11) = _
  rw [poseidon_zero_value_11]
  exact poseidon_zero_step_11

private theorem poseidon_zero_value_13 :
    Poseidon.zeroHash 13 = (0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 12) (Poseidon.zeroHash 12) = _
  rw [poseidon_zero_value_12]
  exact poseidon_zero_step_12

private theorem poseidon_zero_value_14 :
    Poseidon.zeroHash 14 = (0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 13) (Poseidon.zeroHash 13) = _
  rw [poseidon_zero_value_13]
  exact poseidon_zero_step_13

private theorem poseidon_zero_value_15 :
    Poseidon.zeroHash 15 = (0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 14) (Poseidon.zeroHash 14) = _
  rw [poseidon_zero_value_14]
  exact poseidon_zero_step_14

private theorem poseidon_zero_value_16 :
    Poseidon.zeroHash 16 = (0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 15) (Poseidon.zeroHash 15) = _
  rw [poseidon_zero_value_15]
  exact poseidon_zero_step_15

private theorem poseidon_zero_value_17 :
    Poseidon.zeroHash 17 = (0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992 : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 16) (Poseidon.zeroHash 16) = _
  rw [poseidon_zero_value_16]
  exact poseidon_zero_step_16

private theorem poseidon_zero_value_18 :
    Poseidon.zeroHash 18 = (0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 17) (Poseidon.zeroHash 17) = _
  rw [poseidon_zero_value_17]
  exact poseidon_zero_step_17

private theorem poseidon_zero_value_19 :
    Poseidon.zeroHash 19 = (0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 18) (Poseidon.zeroHash 18) = _
  rw [poseidon_zero_value_18]
  exact poseidon_zero_step_18

private theorem poseidon_zero_value_20 :
    Poseidon.zeroHash 20 = (0x2134e76ac5d21aab186c2be1dd8f84ee880a1e46eaf712f9d371b6df22191f3e : F) := by
  change Poseidon.hash2 (Poseidon.zeroHash 19) (Poseidon.zeroHash 19) = _
  rw [poseidon_zero_value_19]
  exact poseidon_zero_step_19

/-- Every constant in the contract's zero table is the corresponding
concrete Poseidon zero hash. -/
theorem poseidon_zero_constants (i : Fin 20) :
    Poseidon.zeroHash i.val = zeroConst i.val := by
  fin_cases i
  · exact poseidon_zero_value_0
  · exact poseidon_zero_value_1
  · exact poseidon_zero_value_2
  · exact poseidon_zero_value_3
  · exact poseidon_zero_value_4
  · exact poseidon_zero_value_5
  · exact poseidon_zero_value_6
  · exact poseidon_zero_value_7
  · exact poseidon_zero_value_8
  · exact poseidon_zero_value_9
  · exact poseidon_zero_value_10
  · exact poseidon_zero_value_11
  · exact poseidon_zero_value_12
  · exact poseidon_zero_value_13
  · exact poseidon_zero_value_14
  · exact poseidon_zero_value_15
  · exact poseidon_zero_value_16
  · exact poseidon_zero_value_17
  · exact poseidon_zero_value_18
  · exact poseidon_zero_value_19

/-- The zero-table equality in the index-and-bound form used by C6. -/
theorem poseidon_zero_constants_lt (l : ℕ) (hl : l < DEPTH) :
    zeroConst l = Poseidon.zeroHash l :=
  (poseidon_zero_constants ⟨l, hl⟩).symm

/-- The contract's empty-root constant is the concrete depth-20 zero hash. -/
theorem poseidon_empty_root :
    Poseidon.zeroHash 20 = (EMPTY_ROOT_CONST : F) := by
  exact poseidon_zero_value_20

#print axioms poseidon_zero_constants
#print axioms poseidon_zero_constants_lt
#print axioms poseidon_empty_root

end MSP
