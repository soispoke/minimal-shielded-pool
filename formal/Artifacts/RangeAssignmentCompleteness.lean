import Artifacts.PinnedRangeCompleteness

/-! Explicit assignment of all 1,080 retained range-bit wires. Source values
and every other wire are preserved; the actual eight range fragments then
follow from their canonical bounds. -/
namespace MSP.Artifacts.RangeAssignmentCompleteness
open MSP.CircuitCompleteness PinnedRangeCompleteness
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def complete (a : Assignment) (wire : ℕ) : F :=
  if 569 ≤ wire ∧ wire < 728 then bitDigit (a 98).val (wire-569)
  else if 13918 ≤ wire ∧ wire < 14045 then bitDigit (a 10).val (wire-13918)
  else if 14045 ≤ wire ∧ wire < 14172 then bitDigit (a 11).val (wire-14045)
  else if 14172 ≤ wire ∧ wire < 14299 then bitDigit (a 94).val (wire-14172)
  else if 14299 ≤ wire ∧ wire < 14426 then bitDigit (a 95).val (wire-14299)
  else if 14426 ≤ wire ∧ wire < 14553 then bitDigit (a 96).val (wire-14426)
  else if 14553 ≤ wire ∧ wire < 14680 then bitDigit (Compression.statement a).fee.val (wire-14553)
  else if 14680 ≤ wire ∧ wire < 14839 then bitDigit (a 97).val (wire-14680)
  else a wire

def written (wire : ℕ) : Prop :=
  (569 ≤ wire ∧ wire < 728) ∨ (13918 ≤ wire ∧ wire < 14839)

theorem preserves (a : Assignment) (wire : ℕ) (h : ¬ written wire) :
    complete a wire = a wire := by
  simp only [written, not_or] at h
  simp only [complete]
  repeat' split
  all_goals first | rfl | omega

theorem preserves_source (a : Assignment) (wire : ℕ) (h : wire < 103) :
    complete a wire = a wire := preserves a wire (by unfold written; omega)

theorem statement_preserved (a : Assignment) :
    Compression.statement (complete a) = Compression.statement a := by
  unfold Compression.statement
  simp only [preserves_source a 99 (by decide), preserves_source a 100 (by decide), preserves_source a 101 (by decide), preserves_source a 102 (by decide), preserves_source a 4 (by decide), preserves_source a 5 (by decide), preserves_source a 96 (by decide), preserves_source a 10 (by decide), preserves_source a 11 (by decide), preserves_source a 94 (by decide), preserves_source a 95 (by decide), preserves_source a 97 (by decide), preserves_source a 98 (by decide)]

theorem authorizer_bits (a : Assignment) (i : ℕ) (h : i < 159) :
    complete a (569+i) = bitDigit (a 98).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem first_input_bits (a : Assignment) (i : ℕ) (h : i < 127) :
    complete a (13918+i) = bitDigit (a 10).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem second_input_bits (a : Assignment) (i : ℕ) (h : i < 127) :
    complete a (14045+i) = bitDigit (a 11).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem first_output_bits (a : Assignment) (i : ℕ) (h : i < 127) :
    complete a (14172+i) = bitDigit (a 94).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem second_output_bits (a : Assignment) (i : ℕ) (h : i < 127) :
    complete a (14299+i) = bitDigit (a 95).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem public_bits (a : Assignment) (i : ℕ) (h : i < 127) :
    complete a (14426+i) = bitDigit (a 96).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem fee_bits (a : Assignment) (i : ℕ) (h : i < 127) :
    complete a (14553+i) = bitDigit (Compression.statement a).fee.val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

theorem recipient_bits (a : Assignment) (i : ℕ) (h : i < 159) :
    complete a (14680+i) = bitDigit (a 97).val i := by
  simp only [complete, Nat.add_sub_cancel_left]
  split_ifs <;> first | omega | rfl

def constraints : List Constraint :=
  RangeData.constraints ++ RangeAmountsData.secondInputConstraints ++
  RangeAmountsData.firstOutputConstraints ++ RangeAmountsData.secondOutputConstraints ++
  RangeAmountsData.publicAmountConstraints ++ RangeAmountsData.feeConstraints ++
  RangeAddressData.recipientConstraints ++ RangeAddressData.authorizerConstraints

def Bounds (a : Assignment) : Prop :=
  (a 10).val < 2^128 ∧ (a 11).val < 2^128 ∧
  (a 94).val < 2^128 ∧ (a 95).val < 2^128 ∧ (a 96).val < 2^128 ∧
  (Compression.statement a).fee.val < 2^128 ∧
  (a 97).val < 2^160 ∧ (a 98).val < 2^160

/-- The constructed bit assignment satisfies all 1,088 actual range constraints. -/
theorem complete_holds (a : Assignment) (hz : a 0 = 1) (h : Bounds a) :
    ∀ c ∈ constraints, c.Holds (complete a) := by
  have hz' : complete a 0 = 1 := (preserves_source a 0 (by decide)).trans hz
  have hs (wire : ℕ) (hw : wire < 103) := preserves_source a wire hw
  obtain ⟨hv0, hv1, hov0, hov1, hp, hf, hr, ha⟩ := h
  have h0 := first_input_complete (complete a) hz'
    (by simpa only [hs 10 (by decide)] using hv0)
    (fun i hi => by simpa only [hs 10 (by decide)] using first_input_bits a i hi)
  have h1 := second_input_complete (complete a) hz'
    (by simpa only [hs 11 (by decide)] using hv1)
    (fun i hi => by simpa only [hs 11 (by decide)] using second_input_bits a i hi)
  have h2 := first_output_complete (complete a) hz'
    (by simpa only [hs 94 (by decide)] using hov0)
    (fun i hi => by simpa only [hs 94 (by decide)] using first_output_bits a i hi)
  have h3 := second_output_complete (complete a) hz'
    (by simpa only [hs 95 (by decide)] using hov1)
    (fun i hi => by simpa only [hs 95 (by decide)] using second_output_bits a i hi)
  have h4 := public_amount_complete (complete a) hz'
    (by simpa only [hs 96 (by decide)] using hp)
    (fun i hi => by simpa only [hs 96 (by decide)] using public_bits a i hi)
  have h5 := fee_complete (complete a) hz'
    (by simpa only [statement_preserved] using hf)
    (fun i hi => by simpa only [statement_preserved] using fee_bits a i hi)
  have h6 := recipient_complete (complete a) hz'
    (by simpa only [hs 97 (by decide)] using hr)
    (fun i hi => by simpa only [hs 97 (by decide)] using recipient_bits a i hi)
  have h7 := authorizer_complete (complete a) hz'
    (by simpa only [hs 98 (by decide)] using ha)
    (fun i hi => by simpa only [hs 98 (by decide)] using authorizer_bits a i hi)
  intro c hc
  simp only [constraints, List.mem_append] at hc
  rcases hc with ((((((hc|hc)|hc)|hc)|hc)|hc)|hc)|hc
  · exact h0 c hc
  · exact h1 c hc
  · exact h2 c hc
  · exact h3 c hc
  · exact h4 c hc
  · exact h5 c hc
  · exact h6 c hc
  · exact h7 c hc

#print axioms complete_holds
end MSP.Artifacts.RangeAssignmentCompleteness
