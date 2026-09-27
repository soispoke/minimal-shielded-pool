import Artifacts.HashAssignmentCompletenessBetaBridge

/-! Transport the already checked beta affine certificates to the generic
completeness interface. Padding each partial-state form by one zero coefficient
matches the existing replaceFirst/withConstants convention exactly. -/

namespace MSP.Artifacts.HashAssignmentCompletenessBetaData

open BetaGates SmallHashGates MSP.Poseidon

set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

private theorem normalize_pad (form : Form) :
    normalize (form ++ constant 0) = normalize form := by
  induction form with
  | nil => simp [constant, BetaGates.normalize, BetaGates.insert]
  | cons term rest ih => simp only [List.cons_append, BetaGates.normalize, ih]

def partialStates (r : Fin 67) (j : Fin 11) : Form :=
  BetaGatesData.partialInput r j ++ constant 0

private theorem partial_state_forms (r : Fin 66) :
    (fun k : Fin 11 => if k = 0 then partialOutputForm circuit r ++
        constant (scheme.partialConstants r) else partialStates r.castSucc k) =
      BetaGates.withConstants
        (BetaGates.replaceFirst (BetaGatesData.partialInput r.castSucc)
          (BetaGatesData.output ⟨87 + r.val, by omega⟩))
        (Optimized.single0 (Optimized.partialConstant r)) := by
  funext k
  by_cases hk : k = 0
  · subst k
    rfl
  · simp only [hk, ↓reduceIte, partialStates, BetaGates.withConstants,
      BetaGates.replaceFirst, Optimized.single0]


def affine : AffineCertificates circuit scheme where
  partialStates := partialStates
  initial := by
    intro j
    exact (fullInput_norm 0 j).trans (BetaGatesCertificates.initial j)
  prefixSteps := by
    intro r j
    have ho := congrArg (fun f => normalize (BetaGates.mixForms Optimized.M
      (BetaGates.withConstants f (Optimized.prefixConstant r.castSucc)) j))
      (fullOutput_prefix r)
    exact (fullInput_norm _ j).trans ((BetaGatesCertificates.prefix_steps r j).trans ho.symm)
  prefixBoundary := by
    intro j
    exact (normalize_pad _).trans
      ((BetaGatesCertificates.prefix_boundary j).trans (prefix_boundary_bridge j).symm)
  partialInputs := by
    intro r
    exact (normalize_pad _).trans (BetaGatesCertificates.partial_inputs r)
  partialSteps := by
    intro r j
    have ho := congrArg (fun f => normalize
      (BetaGates.mixForms (Optimized.sparseMatrix r) f j)) (partial_state_forms r)
    exact (normalize_pad _).trans ((BetaGatesCertificates.partial_steps r j).trans ho.symm)
  partialBoundary := by
    intro j
    exact (fullInput_norm 4 j).trans
      ((BetaGatesCertificates.partial_boundary j).trans (normalize_pad _).symm)
  suffixSteps := by
    intro r j
    have ho := congrArg (fun f => normalize (BetaGates.mixForms Optimized.M
      (BetaGates.withConstants f (Optimized.suffixConstant r)) j))
      (fullOutput_suffix r)
    exact (fullInput_norm _ j).trans ((BetaGatesCertificates.suffix r j).trans ho.symm)
  finalMix := by
    have ho := congrArg (fun f => normalize (BetaGates.mixForms Optimized.M f 0))
      fullOutput_final
    exact BetaGatesCertificates.final_mix.trans ho.symm

end MSP.Artifacts.HashAssignmentCompletenessBetaData
