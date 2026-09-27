import Keccak.Hash

/-! The standard ByteArray.toList implementation uses an opaque well-founded
loop. This proved interface permits kernel evaluation of fixed UTF-8 labels
without replacing their bytes or using native proof evaluation. -/

namespace MSP.Keccak

private theorem byteArray_loop (bs : ByteArray) (i : ℕ) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  rw [ByteArray.toList.loop.eq_1]
  split
  next h =>
    rw [byteArray_loop bs (i+1) (bs.get! i :: r)]
    have hi : i < bs.data.toList.length := by simpa only [Array.length_toList, ByteArray.size] using h
    rw [List.drop_eq_getElem_cons hi, List.reverse_cons, List.append_assoc]
    congr 2
    simp [ByteArray.get!, Array.getElem_toList, h]
  next h =>
    have hi : bs.data.toList.length ≤ i := by simpa only [Array.length_toList, ByteArray.size] using Nat.le_of_not_gt h
    rw [List.drop_eq_nil_of_le hi, List.append_nil]
termination_by bs.size - i

/-- ByteArray conversion agrees with the underlying finite byte sequence. -/
theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [byteArray_loop]
  simp

/-- A computation-friendly theorem for the exact standard UTF-8 encoding. -/
theorem utf8_ofList (cs : List Char) :
    (String.ofList cs).toUTF8.toList = cs.flatMap String.utf8EncodeChar := by
  rw [byteArray_toList, String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  exact List.toList_data_toByteArray

end MSP.Keccak
