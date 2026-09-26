import Spec.Hash

/-!
# C6: the logic's incremental tree

`insert` and `root` mirror `_insert` and `_computeRoot` in
`ShieldedPoolLogic.sol`; step 5 proves the bytecode implements them. The
constants are copied from `_zeros` and `EMPTY_ROOT`.
-/

namespace MSP

/-- `_zeros(l)` for `l < 20`, as in the contract. -/
def ZEROS : List ℕ :=
  [0,
   0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864,
   0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1,
   0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238,
   0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a,
   0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55,
   0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78,
   0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d,
   0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61,
   0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747,
   0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2,
   0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636,
   0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a,
   0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0,
   0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c,
   0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92,
   0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323,
   0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992,
   0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f,
   0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca]

/-- `EMPTY_ROOT` as in the contract. -/
def EMPTY_ROOT_CONST : ℕ := 0x2134e76ac5d21aab186c2be1dd8f84ee880a1e46eaf712f9d371b6df22191f3e

def zeroConst (l : ℕ) : F := (ZEROS.getD l 0 : F)

def CAPACITY : ℕ := 2 ^ DEPTH

/-- `filledSubtrees` and `nextIndex`. -/
structure LogicTree where
  filled : ℕ → F
  next : ℕ

def LogicTree.empty : LogicTree := ⟨fun _ => 0, 0⟩

/-- The `while (idx & 1 == 1)` loop of `_insert`, with fuel above its 20 iterations. -/
def insertLoop (filled : ℕ → F) : F → ℕ → ℕ → ℕ → (ℕ → F)
  | node, _, l, 0 => Function.update filled l node
  | node, idx, l, fuel + 1 =>
      if idx % 2 = 1 then insertLoop filled (H2 (filled l) node) (idx / 2) (l + 1) fuel
      else Function.update filled l node

def LogicTree.insert (t : LogicTree) (c : F) : LogicTree :=
  ⟨insertLoop t.filled c t.next 0 (DEPTH + 1), t.next + 1⟩

/-- `_computeRoot`. -/
def LogicTree.root (t : LogicTree) : F :=
  if t.next = CAPACITY then t.filled DEPTH
  else ((List.range DEPTH).foldl
    (fun (acc : F × ℕ) l =>
      (if acc.2 % 2 = 0 then H2 acc.1 (zeroConst l) else H2 (t.filled l) acc.1, acc.2 / 2))
    (0, t.next)).1

/-- C6. The constants are the zero hashes, and inserting any list of at most
`2 ^ 20` leaves from empty yields the complete tree's root. -/
def C6 : Prop :=
  (∀ l < DEPTH, zeroConst l = Z l) ∧ (EMPTY_ROOT_CONST : F) = EMPTY_ROOT ∧
  ∀ L : List F, L.length ≤ CAPACITY → (L.foldl LogicTree.insert LogicTree.empty).root = TR L

end MSP
