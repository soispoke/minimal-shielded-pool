import Proofs.NonVacuityBytes

/-! Actual calldata and frame encodings used by the W1 witness. All decoding
lemmas use the specification's byte reader, including its concrete offsets. -/

namespace MSP.NonVacuity

def settlementWords (s : SettleData) : List ℕ :=
  [s.root, s.rootSlot, s.epoch, s.domain, s.nf1, s.nf2,
   s.o1, s.o2, s.pub, s.fee, s.rcp, s.auth]

def encodeSettlement (s : SettleData) : List UInt8 :=
  SETTLE_SELECTOR ++ (settlementWords s).flatMap u256

theorem encodeSettlement_length (s : SettleData) :
    (encodeSettlement s).length = 388 := by
  simp only [encodeSettlement, List.length_append, u256_flatMap_length]
  norm_num [SETTLE_SELECTOR, settlementWords]

theorem encodeSettlement_selector (s : SettleData) :
    (encodeSettlement s).take 4 = SETTLE_SELECTOR := by
  exact List.take_left' (by decide : SETTLE_SELECTOR.length = 4)

theorem encodeSettlement_word (s : SettleData) (i : ℕ)
    (hi : i < (settlementWords s).length)
    (hn : (settlementWords s)[i] < 2 ^ 256) :
    wordAt (encodeSettlement s) (4 + 32 * i) = (settlementWords s)[i] := by
  simpa only [List.append_nil, SETTLE_SELECTOR, List.length_cons, List.length_nil,
    Nat.reduceAdd, encodeSettlement] using
    wordAt_prefix_words SETTLE_SELECTOR [] (settlementWords s) i hi hn

theorem decode_encodeSettlement (s : SettleData)
    (hb : ∀ n ∈ settlementWords s, n < 2 ^ 256) :
    SettleData.decode (encodeSettlement s) = s := by
  have hw (i : ℕ) (hi : i < (settlementWords s).length) :=
    encodeSettlement_word s i hi (hb _ (List.getElem_mem hi))
  cases s
  unfold SettleData.decode
  congr 1
  · exact hw 0 (by simp [settlementWords])
  · exact hw 1 (by simp [settlementWords])
  · exact hw 2 (by simp [settlementWords])
  · exact hw 3 (by simp [settlementWords])
  · exact hw 4 (by simp [settlementWords])
  · exact hw 5 (by simp [settlementWords])
  · exact hw 6 (by simp [settlementWords])
  · exact hw 7 (by simp [settlementWords])
  · exact hw 8 (by simp [settlementWords])
  · exact hw 9 (by simp [settlementWords])
  · exact hw 10 (by simp [settlementWords])
  · exact hw 11 (by simp [settlementWords])

def rootFrame (A : ℕ) (s : SettleData) : Frame :=
  ⟨RECENT_ROOT, .verify, 0, 0, 100000, 0,
    u256 (sourceId A s.epoch) ++ u64be s.rootSlot ++ u256 s.root⟩

def verifyFrame (A : ℕ) (π : List UInt8) (b : F) : Frame :=
  ⟨A, .verify, 3, 0, 1000000, 195840, π ++ u256 b.val⟩

def settleFrame (A : ℕ) (s : SettleData) : Frame :=
  ⟨A, .sender, 0, 0, 2000000, 550000, encodeSettlement s⟩

def encodeTx (A c : ℕ) (s : SettleData) (π : List UInt8) (b : F)
    (cost : ℕ) : FrameTx :=
  ⟨c, [min s.nf1 s.nf2, max s.nf1 s.nf2], 0, A,
    [rootFrame A s, verifyFrame A π b, settleFrame A s],
    [⟨1, s.auth, []⟩], [], cost⟩

theorem encodeTx_settleData (A c : ℕ) (s : SettleData) (π : List UInt8)
    (b : F) (cost : ℕ) (hb : ∀ n ∈ settlementWords s, n < 2 ^ 256) :
    settleData (encodeTx A c s π b cost) = s := by
  exact decode_encodeSettlement s hb

theorem encodeTx_proofOf (A c : ℕ) (s : SettleData) (π : List UInt8)
    (b : F) (cost : ℕ) (hπ : π.length = 256) :
    proofOf (encodeTx A c s π b cost) = π := by
  exact List.take_left' hπ

theorem encodeTx_beta (A c : ℕ) (s : SettleData) (π : List UInt8)
    (b : F) (cost : ℕ) (hπ : π.length = 256) :
    wordAt ((encodeTx A c s π b cost).frames.getD 1 default).data 256 = b.val := by
  change wordAt (π ++ u256 b.val) 256 = b.val
  have hp := wordAt_prefix_u256 π [] b.val (lt_trans (ZMod.val_lt b) p_lt)
  simpa only [List.append_nil, hπ] using hp

theorem encodeTx_verifiedPublics (A c : ℕ) (s : SettleData) (π : List UInt8)
    (b : F) (cost : ℕ) (hπ : π.length = 256)
    (hb : ∀ n ∈ settlementWords s, n < 2 ^ 256) :
    verifiedPublics (encodeTx A c s π b cost) =
      (b, γ s.stmt (α s.stmt + b), α s.stmt) := by
  simp only [verifiedPublics, encodeTx_settleData A c s π b cost hb,
    encodeTx_beta A c s π b cost hπ, ZMod.natCast_zmod_val]

/-- Exactly the settlement-field checks in A5, kept separate from encoding. -/
def dataChecks (A c : ℕ) (s : SettleData) : Prop :=
  s.nf1 ≠ 0 ∧ s.nf2 ≠ 0 ∧ s.root < p ∧ s.domain < p ∧ s.nf1 < p ∧ s.nf2 < p ∧
  s.o1 < p ∧ s.o2 < p ∧ s.pub < 2 ^ 128 ∧ s.fee < 2 ^ 128 ∧ s.rcp < 2 ^ 160 ∧
  0 < s.auth ∧ s.auth < 2 ^ 160 ∧ (s.pub = 0 ↔ s.rcp = 0) ∧
  s.domain = (D c A s.epoch).val

/-- The encoded three-frame transaction satisfies every A1--A7 check. -/
theorem encodeTx_Acc (A c : ℕ) (s : SettleData) (π : List UInt8)
    (b : F) (cost : ℕ) (verifies : List UInt8 → F × F × F → Prop)
    (hb : ∀ n ∈ settlementWords s, n < 2 ^ 256)
    (hπ : π.length = 256) (he : s.epoch < 2 ^ 64) (hslot : s.rootSlot < 2 ^ 64)
    (hd : dataChecks A c s) (hq : ∀ j < 8, wordAt π (32 * j) < q)
    (hi : PointsNotInfinity π)
    (hv : verifies π (b, γ s.stmt (α s.stmt + b), α s.stmt))
    (hc : cost ≤ s.fee) :
    Acc A c verifies 1 (encodeTx A c s π b cost) := by
  refine ⟨rootFrame A s, verifyFrame A π b, settleFrame A s, [], rfl, by decide, ?_⟩
  dsimp only [settleFrame]
  rw [decode_encodeSettlement s hb]
  dsimp only [verifyFrame]
  rw [List.take_left' hπ]
  have hw : wordAt (π ++ u256 b.val) 256 = b.val :=
    encodeTx_beta A c s π b cost hπ
  rw [hw]
  simp only [ZMod.natCast_zmod_val]
  refine ⟨?_, ?_, ⟨he, hslot, rfl⟩, ⟨⟨1, s.auth, []⟩, rfl, rfl, rfl, rfl⟩,
    hd, ⟨hq, hi, ZMod.val_lt b, hv⟩, hc⟩
  · simp [encodeTx, rootFrame, hπ, encodeSettlement_length,
      encodeSettlement_selector, u256, u64be, be_length]
  · simp [encodeTx, keysHash, List.append_assoc]

end MSP.NonVacuity
