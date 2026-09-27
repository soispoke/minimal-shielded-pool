import Artifacts.RangeAddressData
import Artifacts.RangeAddressGate
import Artifacts.Spend
import Artifacts.Compression

/-!
# Both actual address range gates

The recipient and authorizer range bounds follow from exact pinned constraints,
including the optimizer's eliminated top bits. Full-system membership and every
field-coefficient reconstruction are checked in Lean. Nonzero authorizer and
other R9 conditions are separate circuit obligations.
-/

namespace MSP.Artifacts.RangeAddress

open RangeAddressData RangeAddressGate RangeLemmas

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem checked_address_range (w : Assignment) (h : Spend.system.Satisfied w)
    (start wire : ℕ) (low : List Constraint) (top : Constraint)
    (hlow : low = (List.range 159).map (lowConstraint start))
    (hm : ∀ c ∈ low ++ [top], c ∈ Spend.system.constraints)
    (ha : top.a = (0, p - 1) :: top.b) (hc : top.c = [])
    (certificate :
      (top.b.map fun t => (t.1, (2 : F)^159 * (t.2 : F))).Perm
        (([(wire, 1)] : LinearCombination).map (fun t => (t.1, (t.2 : F))) ++
          ((weightedWires start 159).map fun t => (t.1, -(t.2 : F))))) :
    (w wire).val < 2^160 := by
  apply gate160_range w h.1 start top (w wire)
  · intro i hi
    apply h.2 _ (hm _ (List.mem_append_left _ ?_))
    rw [hlow]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  · exact h.2 top (hm top (List.mem_append_right _ (by simp)))
  · exact ha
  · exact hc
  · simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using
      reconstruction_of_coefficients top.b [(wire, 1)] start certificate w

/-- Exact location of the recipient gate in the complete pinned constraint list. -/
theorem recipient_eq_slice :
    recipientConstraints = (Spend.group57.drop 46).take 160 := rfl

private theorem recipient_mem {c : Constraint} (hc : c ∈ recipientConstraints) :
    c ∈ Spend.system.constraints := by
  rw [recipient_eq_slice] at hc
  exact List.mem_flatten.mpr
    ⟨Spend.group57, by simp, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

private theorem recipient_low_eq :
    recipientLow = (List.range 159).map (lowConstraint 14680) := rfl

private theorem recipient_coefficients :
    (recipientTop.b.map fun t => (t.1, (2 : F)^159 * (t.2 : F))).Perm
      ((([(97, 1)] : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 14680 159).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Every satisfying assignment of the complete pinned R1CS has a canonical
160-bit recipient value. -/
theorem recipient_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 97).val < 2^160 :=
  checked_address_range w h 14680 97 recipientLow recipientTop
    recipient_low_eq (fun _ hc => recipient_mem hc) (by rfl) (by rfl) recipient_coefficients

/-- Exact location of the authorizer gate in the complete pinned constraint list. -/
theorem authorizer_eq_slice :
    authorizerConstraints = ((Spend.group1 ++ Spend.group2).drop 218).take 160 := rfl

private theorem authorizer_mem {c : Constraint} (hc : c ∈ authorizerConstraints) :
    c ∈ Spend.system.constraints := by
  rw [authorizer_eq_slice] at hc
  have hm := List.mem_of_mem_drop (List.mem_of_mem_take hc)
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_flatten.mpr ⟨Spend.group1, by simp, hm⟩
  · exact List.mem_flatten.mpr ⟨Spend.group2, by simp, hm⟩

private theorem authorizer_low_eq :
    authorizerLow = (List.range 159).map (lowConstraint 569) := rfl

private theorem authorizer_coefficients :
    (authorizerTop.b.map fun t => (t.1, (2 : F)^159 * (t.2 : F))).Perm
      ((([(98, 1)] : LinearCombination).map fun t => (t.1, (t.2 : F))) ++
        ((weightedWires 569 159).map fun t => (t.1, -(t.2 : F)))) := by
  decide

/-- Every satisfying assignment of the complete pinned R1CS has a canonical
160-bit authorizer value. -/
theorem authorizer_range (w : Assignment) (h : Spend.system.Satisfied w) :
    (w 98).val < 2^160 :=
  checked_address_range w h 569 98 authorizerLow authorizerTop
    authorizer_low_eq (fun _ hc => authorizer_mem hc) (by rfl) (by rfl) authorizer_coefficients

/-- Both range bounds for the same statement projection as the compression proof. -/
theorem address_ranges (w : Assignment) (h : Spend.system.Satisfied w) :
    (Compression.statement w).rcp.val < 2^160 ∧
    (Compression.statement w).auth.val < 2^160 :=
  ⟨recipient_range w h, authorizer_range w h⟩

end MSP.Artifacts.RangeAddress
