import Artifacts.HashAssignmentCompleteness
import Artifacts.AssignmentRecoveryBeta
import Artifacts.BetaGatesSigma
import Artifacts.BetaGatesPartialCertificates
import Poseidon.OptimizedEquivalence

/-! The pinned 153-triple beta slice in the generic hash-assignment interface.
All coefficient data is reused from BetaGatesData; no R1CS data is duplicated.
Stage and power-wire descriptors are checked against the existing exact slice. -/

namespace MSP.Artifacts.HashAssignmentCompletenessBetaData

open BetaGates SmallHashGates HashAssignmentCompleteness MSP.Poseidon

set_option maxRecDepth 131072
set_option maxHeartbeats 0

def circuit : Instance where
  name := "main.digest"
  arity := 10
  partialRounds := 66
  tripleCount := 153
  constraints := BetaGatesData.constraints
  constraintCount := rfl
  contains := fun _ h => BetaGates.constraint_mem h
  fullStage r j := if r.val = 0 ∧ j.val = 0 then none
    else some (BetaGatesCertificates.fullIndex r j)
  partialStage r := ⟨87 + r.val, by omega⟩
  foldedInput j := if j.val = 0 then some 0 else none
  inputForms := BetaGatesCertificates.statementForms
  outputForm := [(1, 1)]

def scheme : Scheme 10 66 where
  initialConstants := fun j => Optimized.C ⟨j.val, by omega⟩
  mds := Optimized.M
  preMatrix := Optimized.P
  prefixConstants := Optimized.prefixConstant
  partialConstants := Optimized.partialConstant
  sparseMatrices := Optimized.sparseMatrix
  suffixConstants := Optimized.suffixConstant

theorem scheme_hash (inputs : Fin 10 → F) :
    scheme.hash inputs = Optimized.hash10 inputs := rfl

theorem triple_eq (t : Fin 153) (j : Fin 3) :
    SmallHashGates.triple circuit t j = BetaGatesData.triple t j := rfl

theorem signs (t : Fin 153) : SmallHashGates.TripleSigns circuit t :=
  BetaGatesCertificates.triple_signs t

def stages : StageMap circuit where
  atStage t := if h : t.val < 10 then .inl (0, ⟨t.val + 1, by change t.val + 1 < 11; omega⟩)
    else if h' : t.val < 87 then
      .inl (⟨(t.val - 10) / 11 + 1, by omega⟩, ⟨(t.val - 10) % 11, by change (t.val - 10) % 11 < 11; omega⟩)
    else .inr ⟨t.val - 87, by change t.val - 87 < 66; have := t.isLt; change t.val < 153 at this; omega⟩
  full := by
    intro r j t h
    fin_cases r <;> fin_cases j <;> cases h <;> rfl
  partial_eq := by decide
  valid := by intro t; fin_cases t <;> rfl

def powers : PowerLayout circuit where
  wire k := 263 + 2 * k.1.val + k.2.val
  injective := by
    intro a b h
    have ha := a.2.isLt
    have hb := b.2.isLt
    apply Prod.ext <;> apply Fin.ext <;> dsimp at h ⊢ <;> omega
  nonzero := by intro k; omega
  square := by decide
  fourth := by decide

theorem separate : WriteSeparation powers AssignmentRecoveryBetaData.plan where
  powers := by decide
  inputs := by decide

theorem recovery : RecoveryCorrect circuit AssignmentRecoveryBetaData.plan :=
  AssignmentRecoveryBeta.realizes

/-- The normal forms agree, including the compiler's reordered dense terms. -/
theorem fullInput_norm (r : Fin 8) (j : Fin 11) :
    normalize (fullInputForm circuit scheme.initialConstants r j) =
      normalize (BetaGatesData.fullInput r j) := by
  fin_cases r <;> fin_cases j <;> decide

theorem fullOutput_prefix (r : Fin 3) :
    fullOutputForm circuit scheme.initialConstants ⟨r.val, by omega⟩ =
      BetaGatesData.fullOutput ⟨r.val, by omega⟩ := by
  funext j
  change Fin 11 at j
  fin_cases r <;> fin_cases j <;> rfl

theorem fullOutput_suffix (r : Fin 3) :
    fullOutputForm circuit scheme.initialConstants ⟨r.val + 4, by omega⟩ =
      BetaGatesData.fullOutput ⟨r.val + 4, by omega⟩ := by
  funext j
  change Fin 11 at j
  fin_cases r <;> fin_cases j <;> rfl

theorem fullOutput_final :
    fullOutputForm circuit scheme.initialConstants 7 = BetaGatesData.fullOutput 7 := by
  funext j
  change Fin 11 at j
  fin_cases j <;> rfl

end MSP.Artifacts.HashAssignmentCompletenessBetaData
