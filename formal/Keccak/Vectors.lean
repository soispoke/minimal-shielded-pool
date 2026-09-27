import Keccak.Vector_empty
import Keccak.Vector_abc
import Keccak.Vector_source_one_zero
import Keccak.Vector_rate_minus_one
import Keccak.Vector_rate_exact
import Keccak.Vector_rate_plus_one

namespace MSP.Keccak

attribute [local irreducible] hash

theorem source_one_zero_eq : hash (MSP.addr20 1 ++ MSP.u256 0) =
    0xb9382d35273c75a50631a3e84d3c75ec9266e2b18c35a627e16cdbf26a18ca85 :=
  Vectors.source_one_zero.hash_eq

theorem source_one_zero_nondegenerate :
    2^64 ≤ hash (MSP.addr20 1 ++ MSP.u256 0) := by
  rw [source_one_zero_eq]
  decide

#print axioms hash_lt
#print axioms word_toNat
#print axioms pad_length
#print axioms Vectors.empty.hash_eq
#print axioms Vectors.abc.hash_eq
#print axioms source_one_zero_eq
#print axioms source_one_zero_nondegenerate
#print axioms Vectors.rate_minus_one.hash_eq
#print axioms Vectors.rate_exact.hash_eq
#print axioms Vectors.rate_plus_one.hash_eq

end MSP.Keccak
