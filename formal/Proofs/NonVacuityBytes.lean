import Proofs.C3

/-! Byte-level round trips for the concrete non-vacuity frame constructor. -/

namespace MSP

/-- Interpret a byte list as an unsigned big-endian natural number. -/
def readBE (bytes : List UInt8) : ℕ :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem readBE_acc (bytes : List UInt8) (acc : ℕ) :
    bytes.foldl (fun acc b => acc * 256 + b.toNat) acc =
      acc * 256 ^ bytes.length + readBE bytes := by
  induction bytes generalizing acc with
  | nil => simp [readBE]
  | cons b bytes ih =>
    simp only [List.foldl_cons, List.length_cons, readBE]
    rw [ih (acc * 256 + b.toNat), ih (0 * 256 + b.toNat)]
    simp only [readBE, pow_succ]
    ring

theorem readBE_cons (b : UInt8) (bytes : List UInt8) :
    readBE (b :: bytes) = b.toNat * 256 ^ bytes.length + readBE bytes := by
  simp only [readBE, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  exact readBE_acc bytes b.toNat

theorem readBE_be (k n : ℕ) : readBE (be k n) = n % 256 ^ k := by
  induction k with
  | zero => simp [be, readBE, Nat.mod_one]
  | succ k ih =>
    rw [be_succ, readBE_cons, be_length, ih]
    rw [UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide))]
    rw [Nat.mod_pow_succ]
    ring

/-- Reading a complete encoded word ignores any following payload. -/
theorem wordAt_u256_mod (n : ℕ) (tail : List UInt8) :
    wordAt (u256 n ++ tail) 0 = n % 2 ^ 256 := by
  have hl : (u256 n).length = 32 := be_length 32 n
  unfold wordAt
  simp only [List.drop_zero]
  rw [List.take_left' hl, List.take_left' hl]
  change readBE (be 32 n) = _
  rw [readBE_be]
  norm_num

theorem wordAt_u256 (n : ℕ) (tail : List UInt8) (hn : n < 2 ^ 256) :
    wordAt (u256 n ++ tail) 0 = n := by
  rw [wordAt_u256_mod, Nat.mod_eq_of_lt hn]

/-- Removing an arbitrary pre shifts the actual byte-reader's offset. -/
theorem wordAt_append_length (pre bytes : List UInt8) (off : ℕ) :
    wordAt (pre ++ bytes) (pre.length + off) = wordAt bytes off := by
  simp only [wordAt, List.drop_length_add_append]

theorem wordAt_prefix_u256 (pre tail : List UInt8) (n : ℕ) (hn : n < 2 ^ 256) :
    wordAt (pre ++ u256 n ++ tail) pre.length = n := by
  rw [List.append_assoc]
  have h := wordAt_append_length pre (u256 n ++ tail) 0
  simpa only [Nat.add_zero, wordAt_u256 n tail hn] using h

theorem u256_flatMap_length (words : List ℕ) :
    (words.flatMap u256).length = 32 * words.length := by
  induction words with
  | nil => simp
  | cons n words ih => simp [List.flatMap_cons, u256, be_length, ih, Nat.mul_add, Nat.add_comm]

/-- Reading any selected word of a concatenated encoding, with arbitrary tail. -/
theorem wordAt_words (words : List ℕ) (tail : List UInt8) (i : ℕ)
    (hi : i < words.length) (hn : words[i] < 2 ^ 256) :
    wordAt (words.flatMap u256 ++ tail) (32 * i) = words[i] := by
  induction words generalizing i with
  | nil => simp at hi
  | cons n words ih =>
    cases i with
    | zero =>
      simpa only [List.flatMap_cons, List.append_assoc, Nat.mul_zero, List.getElem_cons_zero]
        using wordAt_u256 n (words.flatMap u256 ++ tail) hn
    | succ i =>
      have hl : (u256 n).length = 32 := be_length 32 n
      have hoff : 32 * (i + 1) = (u256 n).length + 32 * i := by rw [hl]; omega
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_succ]
      rw [hoff, wordAt_append_length]
      exact ih i (by simpa using hi) hn

theorem wordAt_prefix_words (pre tail : List UInt8) (words : List ℕ) (i : ℕ)
    (hi : i < words.length) (hn : words[i] < 2 ^ 256) :
    wordAt (pre ++ words.flatMap u256 ++ tail) (pre.length + 32 * i) = words[i] := by
  rw [List.append_assoc, wordAt_append_length]
  exact wordAt_words words tail i hi hn

end MSP
