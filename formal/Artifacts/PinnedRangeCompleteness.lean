import Artifacts.RangeCompleteness
import Artifacts.RangeAmounts
import Artifacts.RangeAddress

/-! Completeness of the eight actual optimized range fragments. A candidate
assignment with canonical retained bit wires satisfies every range constraint.
The coefficient and shape facts are checked here against pinned data, without
assuming any constraint holds. Constructing all circuit wires remains separate. -/

namespace MSP.Artifacts.PinnedRangeCompleteness

open RangeLemmas RangeGate MSP.CircuitCompleteness

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem complete_list (a : Assignment) (hzero : a 0 = 1)
    (start n : ℕ) (low : List Constraint) (top : Constraint) (x : F)
    (hx : x.val < 2^(n+1))
    (hbits : ∀ i < n, a (start+i) = bitDigit x.val i)
    (hlow : low = (List.range n).map (lowConstraint start))
    (ha : top.a = (0,p-1) :: top.b) (hc : top.c = [])
    (hrec : (weightedWires start n).eval a + (2:F)^n * top.b.eval a = x) :
    ∀ c ∈ low ++ [top], c.Holds a := by
  have gates := RangeCompleteness.gate_complete a hzero start n top x hx hbits ha hc hrec
  intro c hmem
  rcases List.mem_append.mp hmem with hl | ht
  · rw [hlow] at hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    exact gates.1 i (List.mem_range.mp hi)
  · have heq := List.mem_singleton.mp ht
    simpa only [heq] using gates.2

/-- Every constraint of the pinned first input range gate holds. -/
theorem first_input_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 10).val < 2^128)
    (hbits : ∀ i < 127, a (13918+i) = bitDigit (a 10).val i) :
    ∀ c ∈ RangeData.constraints, c.Holds a := by
  apply complete_list a hzero 13918 127 RangeData.lowConstraints RangeData.topConstraint (a 10) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeGate.reconstruction_of_coefficients RangeData.topConstraint.b
    ([( 10, 1)] : LinearCombination) 13918 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

/-- Every constraint of the pinned second input range gate holds. -/
theorem second_input_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 11).val < 2^128)
    (hbits : ∀ i < 127, a (14045+i) = bitDigit (a 11).val i) :
    ∀ c ∈ RangeAmountsData.secondInputConstraints, c.Holds a := by
  apply complete_list a hzero 14045 127 RangeAmountsData.secondInputLow RangeAmountsData.secondInputTop (a 11) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeGate.reconstruction_of_coefficients RangeAmountsData.secondInputTop.b
    ([( 11, 1)] : LinearCombination) 14045 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

/-- Every constraint of the pinned first output range gate holds. -/
theorem first_output_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 94).val < 2^128)
    (hbits : ∀ i < 127, a (14172+i) = bitDigit (a 94).val i) :
    ∀ c ∈ RangeAmountsData.firstOutputConstraints, c.Holds a := by
  apply complete_list a hzero 14172 127 RangeAmountsData.firstOutputLow RangeAmountsData.firstOutputTop (a 94) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeGate.reconstruction_of_coefficients RangeAmountsData.firstOutputTop.b
    ([( 94, 1)] : LinearCombination) 14172 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

/-- Every constraint of the pinned second output range gate holds. -/
theorem second_output_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 95).val < 2^128)
    (hbits : ∀ i < 127, a (14299+i) = bitDigit (a 95).val i) :
    ∀ c ∈ RangeAmountsData.secondOutputConstraints, c.Holds a := by
  apply complete_list a hzero 14299 127 RangeAmountsData.secondOutputLow RangeAmountsData.secondOutputTop (a 95) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeGate.reconstruction_of_coefficients RangeAmountsData.secondOutputTop.b
    ([( 95, 1)] : LinearCombination) 14299 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

/-- Every constraint of the pinned public amount range gate holds. -/
theorem public_amount_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 96).val < 2^128)
    (hbits : ∀ i < 127, a (14426+i) = bitDigit (a 96).val i) :
    ∀ c ∈ RangeAmountsData.publicAmountConstraints, c.Holds a := by
  apply complete_list a hzero 14426 127 RangeAmountsData.publicAmountLow RangeAmountsData.publicAmountTop (a 96) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeGate.reconstruction_of_coefficients RangeAmountsData.publicAmountTop.b
    ([( 96, 1)] : LinearCombination) 14426 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

/-- Every constraint of the pinned fee range gate holds. -/
theorem fee_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : ((Compression.statement a).fee).val < 2^128)
    (hbits : ∀ i < 127, a (14553+i) = bitDigit ((Compression.statement a).fee).val i) :
    ∀ c ∈ RangeAmountsData.feeConstraints, c.Holds a := by
  apply complete_list a hzero 14553 127 RangeAmountsData.feeLow RangeAmountsData.feeTop ((Compression.statement a).fee) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeGate.reconstruction_of_coefficients RangeAmountsData.feeTop.b
    RangeAmounts.feeAmount 14553 (by decide) a
  simpa only [RangeAmounts.feeAmount_eval] using hrec

/-- Every constraint of the pinned recipient range gate holds. -/
theorem recipient_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 97).val < 2^160)
    (hbits : ∀ i < 159, a (14680+i) = bitDigit (a 97).val i) :
    ∀ c ∈ RangeAddressData.recipientConstraints, c.Holds a := by
  apply complete_list a hzero 14680 159 RangeAddressData.recipientLow RangeAddressData.recipientTop (a 97) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeAddressGate.reconstruction_of_coefficients RangeAddressData.recipientTop.b
    ([( 97, 1)] : LinearCombination) 14680 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

/-- Every constraint of the pinned authorizer range gate holds. -/
theorem authorizer_complete (a : Assignment) (hzero : a 0 = 1)
    (hx : (a 98).val < 2^160)
    (hbits : ∀ i < 159, a (569+i) = bitDigit (a 98).val i) :
    ∀ c ∈ RangeAddressData.authorizerConstraints, c.Holds a := by
  apply complete_list a hzero 569 159 RangeAddressData.authorizerLow RangeAddressData.authorizerTop (a 98) hx hbits
    (by rfl) (by rfl) (by rfl)
  have hrec := RangeAddressGate.reconstruction_of_coefficients RangeAddressData.authorizerTop.b
    ([( 98, 1)] : LinearCombination) 569 (by decide) a
  simpa only [LinearCombination.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero] using hrec

#print axioms first_input_complete
#print axioms second_input_complete
#print axioms first_output_complete
#print axioms second_output_complete
#print axioms public_amount_complete
#print axioms fee_complete
#print axioms recipient_complete
#print axioms authorizer_complete

end MSP.Artifacts.PinnedRangeCompleteness
