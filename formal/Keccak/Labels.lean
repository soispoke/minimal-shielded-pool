import Keccak.Encoding
import Keccak.Vector_abc
import Keccak.Vector_domain_tag
import Keccak.Vector_rr_entry_tag
import Keccak.Vector_rr_storage_tag
import Keccak.Vector_domain_one_one_zero

namespace MSP.Keccak

attribute [local irreducible] hash

theorem abc_bytes : "abc".toUTF8.toList = Vectors.abc.input := by
  rw [show "abc" = String.ofList ['a', 'b', 'c'] from rfl, utf8_ofList]
  decide

theorem abc_eq : hash "abc".toUTF8.toList = 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45 := by
  rw [abc_bytes]
  exact Vectors.abc.hash_eq

theorem domain_tag_bytes : "minimal-shielded-pool:occurrence-domain:v1".toUTF8.toList = Vectors.domain_tag.input := by
  rw [show "minimal-shielded-pool:occurrence-domain:v1" = String.ofList ['m', 'i', 'n', 'i', 'm', 'a', 'l', '-', 's', 'h', 'i', 'e', 'l', 'd', 'e', 'd', '-', 'p', 'o', 'o', 'l', ':', 'o', 'c', 'c', 'u', 'r', 'r', 'e', 'n', 'c', 'e', '-', 'd', 'o', 'm', 'a', 'i', 'n', ':', 'v', '1'] from rfl, utf8_ofList]
  decide

theorem domain_tag_eq : hash "minimal-shielded-pool:occurrence-domain:v1".toUTF8.toList = 0xa9d03fa1cd97bcf3294dc8e3bb024f555393c98967b356967fa502abab366ed3 := by
  rw [domain_tag_bytes]
  exact Vectors.domain_tag.hash_eq

theorem rr_entry_tag_bytes : "RECENT_ROOT_ENTRY".toUTF8.toList = Vectors.rr_entry_tag.input := by
  rw [show "RECENT_ROOT_ENTRY" = String.ofList ['R', 'E', 'C', 'E', 'N', 'T', '_', 'R', 'O', 'O', 'T', '_', 'E', 'N', 'T', 'R', 'Y'] from rfl, utf8_ofList]
  decide

theorem rr_entry_tag_eq : hash "RECENT_ROOT_ENTRY".toUTF8.toList = 0x8f42481679c8e6fefa040974b3c905e0ce3f2e464ba93acdb074a41181617efc := by
  rw [rr_entry_tag_bytes]
  exact Vectors.rr_entry_tag.hash_eq

theorem rr_storage_tag_bytes : "RECENT_ROOT_STORAGE".toUTF8.toList = Vectors.rr_storage_tag.input := by
  rw [show "RECENT_ROOT_STORAGE" = String.ofList ['R', 'E', 'C', 'E', 'N', 'T', '_', 'R', 'O', 'O', 'T', '_', 'S', 'T', 'O', 'R', 'A', 'G', 'E'] from rfl, utf8_ofList]
  decide

theorem rr_storage_tag_eq : hash "RECENT_ROOT_STORAGE".toUTF8.toList = 0xbdc897da2177d260ff5f4be5d4b2aad43f89c3347a305b584fa5a2546d053daa := by
  rw [rr_storage_tag_bytes]
  exact Vectors.rr_storage_tag.hash_eq

theorem domain_one_one_zero_eq :
    hash (MSP.u256 (hash "minimal-shielded-pool:occurrence-domain:v1".toUTF8.toList) ++
      MSP.u256 1 ++ MSP.u256 1 ++ MSP.u256 0) =
      0xfcf197a9fa8d33889e20bb0e25a307f6358795fbade02203070a17ceb0c20130 := by
  rw [domain_tag_eq]
  exact Vectors.domain_one_one_zero.hash_eq

#print axioms byteArray_toList
#print axioms utf8_ofList
#print axioms domain_tag_eq
#print axioms rr_entry_tag_eq
#print axioms rr_storage_tag_eq
#print axioms domain_one_one_zero_eq

end MSP.Keccak
