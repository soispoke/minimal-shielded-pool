import Artifacts.SmallHashGates
import Artifacts.SmallHashGatesInterface
import Poseidon.Optimized3Equivalence
import Poseidon.Optimized4Equivalence

/-! A width-generic optimized schedule and its explicit affine certificate boundary.
The two concrete schemes below are definitionally the pinned optimized models.
-/

namespace MSP.Artifacts.SmallHashGates

open BetaGates MSP.Poseidon

structure Scheme (arity rp : ℕ) where
  initialConstants : Fin (arity + 1) → F
  mds : Matrix (Fin (arity + 1)) (Fin (arity + 1)) F
  preMatrix : Matrix (Fin (arity + 1)) (Fin (arity + 1)) F
  prefixConstants : Fin 4 → Fin (arity + 1) → F
  partialConstants : Fin rp → F
  sparseMatrices : Fin rp → Matrix (Fin (arity + 1)) (Fin (arity + 1)) F
  suffixConstants : Fin 3 → Fin (arity + 1) → F

namespace Scheme

variable {arity rp : ℕ} (s : Scheme arity rp)

def initialState (inputs : Fin arity → F) : Fin (arity + 1) → F := fun i =>
  (if h : i.val = 0 then 0 else inputs ⟨i.val - 1, by omega⟩) + s.initialConstants i

def prefixStep (r : Fin 4) (state : Fin (arity + 1) → F) : Fin (arity + 1) → F :=
  Matrix.vecMul ((fun i => (state i)^5) + s.prefixConstants r)
    (if r.val = 3 then s.preMatrix else s.mds)

def partialStep (r : Fin rp) (state : Fin (arity + 1) → F) : Fin (arity + 1) → F :=
  Matrix.vecMul ((fun i => if i = 0 then (state i)^5 else state i) +
    (fun i => if i = 0 then s.partialConstants r else 0)) (s.sparseMatrices r)

def suffixStep (r : Fin 3) (state : Fin (arity + 1) → F) : Fin (arity + 1) → F :=
  Matrix.vecMul ((fun i => (state i)^5) + s.suffixConstants r) s.mds

def prefixState (inputs : Fin arity → F) : Fin (arity + 1) → F :=
  (List.finRange 4).foldl (fun a r => s.prefixStep r a) (s.initialState inputs)

def partialState (inputs : Fin arity → F) : Fin (arity + 1) → F :=
  (List.finRange rp).foldl (fun a r => s.partialStep r a) (s.prefixState inputs)

def suffixState (inputs : Fin arity → F) : Fin (arity + 1) → F :=
  (List.finRange 3).foldl (fun a r => s.suffixStep r a) (s.partialState inputs)

def hash (inputs : Fin arity → F) : F :=
  (Matrix.vecMul (fun i => (s.suffixState inputs i)^5) s.mds) 0

end Scheme

def scheme3 : Scheme 2 57 where
  initialConstants := fun i => Optimized3.C ⟨i.val, by omega⟩
  mds := Optimized3.M
  preMatrix := Optimized3.P
  prefixConstants := Optimized3.prefixConstant
  partialConstants := Optimized3.partialConstant
  sparseMatrices := Optimized3.sparseMatrix
  suffixConstants := Optimized3.suffixConstant

def scheme4 : Scheme 3 56 where
  initialConstants := fun i => Optimized4.C ⟨i.val, by omega⟩
  mds := Optimized4.M
  preMatrix := Optimized4.P
  prefixConstants := Optimized4.prefixConstant
  partialConstants := Optimized4.partialConstant
  sparseMatrices := Optimized4.sparseMatrix
  suffixConstants := Optimized4.suffixConstant

theorem scheme3_hash (inputs : Fin 2 → F) : scheme3.hash inputs = Optimized3.hash2 inputs := rfl
theorem scheme4_hash (inputs : Fin 3 → F) : scheme4.hash inputs = Optimized4.hash3 inputs := rfl

def initialForms (g : Instance) (s : Scheme g.arity g.partialRounds) : Fin (g.arity + 1) → Form :=
  fun i => (if h : i.val = 0 then [] else g.inputForms ⟨i.val - 1, by omega⟩) ++
    constant (s.initialConstants i)

/-- These finite coefficient equations are precisely the remaining affine work.
Every equation is checked after normalization, whose evaluation soundness is proved.
No field-valued hash result is a premise of this certificate. -/
structure AffineCertificates (g : Instance) (s : Scheme g.arity g.partialRounds) where
  partialStates : Fin (g.partialRounds + 1) → Fin (g.arity + 1) → Form
  initial : ∀ j, normalize (fullInputForm g s.initialConstants 0 j) = normalize (initialForms g s j)
  prefixSteps : ∀ (r : Fin 3) j,
    normalize (fullInputForm g s.initialConstants ⟨r.val + 1, by omega⟩ j) =
      normalize (mixForms s.mds
        (withConstants (fullOutputForm g s.initialConstants ⟨r.val, by omega⟩)
          (s.prefixConstants r.castSucc)) j)
  prefixBoundary : ∀ j, normalize (partialStates 0 j) =
    normalize (mixForms s.preMatrix
      (withConstants (fullOutputForm g s.initialConstants 3) (s.prefixConstants 3)) j)
  partialInputs : ∀ r, normalize (partialStates r.castSucc 0) = normalize (partialInputForm g r)
  partialSteps : ∀ r j, normalize (partialStates r.succ j) =
    normalize (mixForms (s.sparseMatrices r)
      (fun k => if k = 0 then partialOutputForm g r ++ constant (s.partialConstants r)
        else partialStates r.castSucc k) j)
  partialBoundary : ∀ j, normalize (fullInputForm g s.initialConstants 4 j) =
    normalize (partialStates (Fin.last g.partialRounds) j)
  suffixSteps : ∀ (r : Fin 3) j,
    normalize (fullInputForm g s.initialConstants ⟨r.val + 5, by omega⟩ j) =
      normalize (mixForms s.mds
        (withConstants (fullOutputForm g s.initialConstants ⟨r.val + 4, by omega⟩)
          (s.suffixConstants r)) j)
  finalMix : normalize g.outputForm =
    normalize (mixForms s.mds (fullOutputForm g s.initialConstants 7) 0)

end MSP.Artifacts.SmallHashGates
