import Artifacts.BetaGatesData

/-! Kernel-checked coefficient certificates. None asserts correctness by execution
of an external program, and none assumes the hash conclusion being proved. -/

namespace MSP.Artifacts.BetaGatesCertificates

open BetaGates BetaGatesData
open MSP.Poseidon

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def TripleSigns (t : Fin 153) : Prop :=
  normalize (ofLC (triple t 0).a) = normalize (scale (-1) (input t)) ∧
  normalize (ofLC (triple t 0).c) = normalize (scale (-1) (ofLC (triple t 1).b)) ∧
  normalize (ofLC (triple t 1).a) = normalize (scale (-1) (ofLC (triple t 1).b)) ∧
  normalize (ofLC (triple t 2).a) = normalize (ofLC (triple t 1).c) ∧
  normalize (ofLC (triple t 2).b) = normalize (input t)

theorem triple_signs : ∀ t, TripleSigns t := by
  unfold TripleSigns
  decide

def fullIndex (r : Fin 8) (i : Fin 11) : Fin 153 :=
  if r.val = 0 then ⟨i.val - 1, by omega⟩
  else ⟨10 + 11 * (r.val - 1) + i.val, by omega⟩

theorem full_inputs : ∀ (r : Fin 8) (i : Fin 11),
    normalize (fullInput r i) = normalize
      (if r.val = 0 ∧ i.val = 0 then constant (Optimized.C 0) else input (fullIndex r i)) := by decide

theorem full_outputs : ∀ (r : Fin 8) (i : Fin 11),
    normalize (fullOutput r i) = normalize
      (if r.val = 0 ∧ i.val = 0 then constant ((Optimized.C 0)^5) else output (fullIndex r i)) := by decide

def statementForms : Fin 10 → Form :=
  ![[(99, 1)], [(100, 1)], [(101, 1)], [(102, 1)], [(4, 1)], [(5, 1)], [(96, 1)],
    [(10, 1), (11, 1), (94, -1), (95, -1), (96, -1)], [(97, 1)], [(98, 1)]]

def initialForms : Fin 11 → Form := fun i =>
  (if h : i.val = 0 then [] else statementForms ⟨i.val - 1, by omega⟩) ++
    constant (Optimized.C ⟨i.val, by omega⟩)

theorem initial : ∀ i, normalize (fullInput 0 i) = normalize (initialForms i) := by decide

theorem prefix_steps : ∀ (r : Fin 3) (i : Fin 11),
    normalize (fullInput ⟨r.val + 1, by omega⟩ i) =
      normalize (mixForms Optimized.M
        (withConstants (fullOutput ⟨r.val, by omega⟩) (Optimized.prefixConstant r.castSucc)) i) := by decide

theorem prefix_boundary : ∀ i,
    normalize (partialInput 0 i) =
      normalize (mixForms Optimized.P (withConstants (fullOutput 3) (Optimized.prefixConstant 3)) i) := by decide

theorem partial_inputs : ∀ (r : Fin 66),
    normalize (partialInput r.castSucc 0) = normalize (input ⟨87 + r.val, by omega⟩) := by decide

def PartialStepCertificate (r : Fin 66) : Prop := ∀ i,
    normalize (partialInput r.succ i) =
      normalize (mixForms (Optimized.sparseMatrix r)
        (withConstants (replaceFirst (partialInput r.castSucc) (output ⟨87 + r.val, by omega⟩))
          (Optimized.single0 (Optimized.partialConstant r))) i)

theorem partial_boundary : ∀ i,
    normalize (fullInput 4 i) = normalize (partialInput 66 i) := by decide

theorem suffix : ∀ (r : Fin 3) (i : Fin 11),
    normalize (fullInput ⟨r.val + 5, by omega⟩ i) =
      normalize (mixForms Optimized.M
        (withConstants (fullOutput ⟨r.val + 4, by omega⟩) (Optimized.suffixConstant r)) i) := by decide

theorem final_mix : normalize [(1, 1)] = normalize (mixForms Optimized.M (fullOutput 7) 0) := by decide

end MSP.Artifacts.BetaGatesCertificates
