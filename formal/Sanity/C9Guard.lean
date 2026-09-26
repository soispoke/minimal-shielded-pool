import Spec

namespace MSP
noncomputable section
open Classical

/-- Acc's proof words are `proofOf tx`, of length 256, so C9's guard always applies,
and with C9 an approved spend's proof is one Groth16 accepts for `verifiedPublics`. -/
theorem acc_groth16 (d : Deployment) (hd : Honest d) (hC9 : C9) (tx : FrameTx)
    (h : Acc (addrOf d) (chainOf d) (verifierOf d) 1 tx) :
    (proofOf tx).length = 256 ∧ Groth16Accepts (proofOf tx) (verifiedPublics tx) := by
  obtain ⟨f0, f1, f2, rest, hfr, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hlen, -⟩, -, -, -, -, ⟨-, -, -, hv⟩, -⟩ := h
  have hp : proofOf tx = f1.data.take 256 := by simp [proofOf, hfr]
  have hl : (proofOf tx).length = 256 := by rw [hp, List.length_take, hlen]; rfl
  refine ⟨hl, ?_⟩
  have hvp : verifiedPublics tx = ((wordAt f1.data 256 : F),
      γ (SettleData.decode f2.data).stmt (α (SettleData.decode f2.data).stmt + (wordAt f1.data 256 : F)),
      α (SettleData.decode f2.data).stmt) := by simp [verifiedPublics, settleData, hfr]
  rw [hvp, ← (hC9 d hd _ _ hl), hp]
  exact hv

#print axioms acc_groth16
end
end MSP
