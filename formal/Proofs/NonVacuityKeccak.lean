import Spec.FrameTx
import Keccak.Vectors
import Keccak.Labels

/-! Exact Keccak constants for the W1 candidate. These are consequences of the
concrete reference hash and its kernel-checked round witnesses, not additional
cryptographic assumptions. -/

namespace MSP.NonVacuity

attribute [local irreducible] Keccak.hash

theorem sourceId_one_zero_eq : sourceId 1 0 =
    83777132435126701296934365153674188610954941488820807845617732241460198689413 := by
  unfold sourceId K
  exact Keccak.source_one_zero_eq

theorem sourceId_one_zero_nondegenerate : 2^64 ≤ sourceId 1 0 := by
  rw [sourceId_one_zero_eq]
  decide

theorem domain_tag_eq : DOMAIN_TAG =
    76808814772268626012210632844915455429679029209726038474055044870401301049043 := by
  unfold DOMAIN_TAG K
  exact Keccak.domain_tag_eq

theorem rr_entry_domain_eq : RR_ENTRY_DOMAIN =
    64797846785363696217070492401087454540399578079710875804726939730834826034940 := by
  unfold RR_ENTRY_DOMAIN K
  exact Keccak.rr_entry_tag_eq

theorem rr_storage_domain_eq : RR_STORAGE_DOMAIN =
    85841545839684360533941767083239388277786941952095340532316774039329232469418 := by
  unfold RR_STORAGE_DOMAIN K
  exact Keccak.rr_storage_tag_eq

theorem domain_one_one_zero_eq : D 1 1 0 =
    (4968480372713856270053508398811659268951190880053845541428304835575363535147 : F) := by
  unfold D DOMAIN_TAG K
  rw [Keccak.domain_one_one_zero_eq]
  decide

theorem domain_one_one_zero_val : (D 1 1 0).val =
    4968480372713856270053508398811659268951190880053845541428304835575363535147 := by
  rw [domain_one_one_zero_eq]
  decide

#print axioms sourceId_one_zero_eq
#print axioms sourceId_one_zero_nondegenerate
#print axioms domain_one_one_zero_eq
#print axioms domain_one_one_zero_val

end MSP.NonVacuity
