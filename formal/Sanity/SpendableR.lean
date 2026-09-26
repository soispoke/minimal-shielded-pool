import Spec

/-! The canonical spend `mkSpend` satisfies `R` given only the facts
Spendable's proof can obtain: the value range from C5a, the tree lemma for R3,
and the two hash inequalities a run without a bad event gives. A cast or index
slip in `mkSpend`, `R` or `SINK` would make this fail. -/

namespace MSP
noncomputable section
open Classical

theorem mkSpend_R (P : Pool) (e : ℕ) (L : List F) (i : ℕ) (sk ρ v skd ρd f rcp auth : F)
    (hi : i < 2 ^ DEPTH) (hv : v.val < 2 ^ 128) (hf : f.val < v.val)
    (hrcp0 : 0 < rcp.val) (hrcp : rcp.val < 2 ^ 160) (ha0 : 0 < auth.val) (ha : auth.val < 2 ^ 160)
    (hR3 : v ≠ 0 → MR ((mkSpend P e L i sk ρ v skd ρd f rcp auth).2.leaf 0) i (siblingsOf L i) = TR L)
    (hnf : (mkSpend P e L i sk ρ v skd ρd f rcp auth).1.nf1 ≠ (mkSpend P e L i sk ρ v skd ρd f rcp auth).1.nf2)
    (hsink : SINK 0 ≠ SINK 1) :
    R (mkSpend P e L i sk ρ v skd ρd f rcp auth).1 (mkSpend P e L i sk ρ v skd ρd f rcp auth).2 := by
  have hvf : (v - f).val = v.val - f.val := by
    rw [ZMod.val_sub (le_of_lt hf)]
  have hpub0 : v - f ≠ 0 := by
    intro h; rw [h, ZMod.val_zero] at hvf; omega
  have hrcpne : rcp ≠ 0 := by intro h; rw [h, ZMod.val_zero] at hrcp0; omega
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnf, ?_, ?_, ha0, ha, ?_⟩
  · intro k; fin_cases k <;> simp [mkSpend] <;> omega
  · intro k hk; fin_cases k
    · exact hR3 (by simpa [mkSpend] using hk)
    · simp [mkSpend] at hk
  · simp [mkSpend, SINK]
  · simp [mkSpend, SINK]
  · simp only [mkSpend, List.mem_cons, List.not_mem_nil, or_false]
    rintro y (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [ZMod.val_zero, hvf] <;> omega
  · simp [mkSpend, ZMod.val_zero, hvf]; omega
  · simp [mkSpend, ZMod.val_zero]; intro h; rw [h, ZMod.val_zero] at hf; omega
  · intro k; fin_cases k <;> simp [mkSpend]
  · simpa [mkSpend] using hsink
  · simpa [mkSpend] using hrcp
  · simp [mkSpend, hpub0, hrcpne]

end
end MSP

#print axioms MSP.mkSpend_R
