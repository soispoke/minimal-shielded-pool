import Poseidon.OptimizedData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The exact width-11 optimized circomlib schedule. Its equivalence to the
ordinary reference is proved separately; the R1CS binding is also separate. -/

namespace MSP.Poseidon.Optimized

def mix (m : Matrix11) (s : State) : State := Matrix.vecMul s m
def sbox (s : State) : State := fun i => s i ^ 5
def partialSbox (s : State) : State := fun i => if i = 0 then s i ^ 5 else s i
def single0 (d : F) : State := fun i => if i = 0 then d else 0

def prefixConstant (r : Fin 4) : State := fun i => C ⟨11 + 11 * r.val + i.val, by omega⟩
def partialConstant (r : Fin 66) : F := C ⟨55 + r.val, by omega⟩
def suffixConstant (r : Fin 3) : State := fun i => C ⟨121 + 11 * r.val + i.val, by omega⟩

def prefixStep (r : Fin 4) (s : State) : State :=
  mix (if r.val = 3 then P else M) (sbox s + prefixConstant r)

def partialStep (r : Fin 66) (s : State) : State :=
  mix (sparseMatrix r) (partialSbox s + single0 (partialConstant r))

def suffixStep (r : Fin 3) (s : State) : State :=
  mix M (sbox s + suffixConstant r)

def initialState (inputs : Fin 10 → F) : State := fun i =>
  (if h : i.val = 0 then 0 else inputs ⟨i.val - 1, by omega⟩) + C ⟨i.val, by omega⟩

def prefixState (inputs : Fin 10 → F) : State :=
  (List.finRange 4).foldl (fun s r => prefixStep r s) (initialState inputs)

def partialState (inputs : Fin 10 → F) : State :=
  (List.finRange 66).foldl (fun s r => partialStep r s) (prefixState inputs)

def suffixState (inputs : Fin 10 → F) : State :=
  (List.finRange 3).foldl (fun s r => suffixStep r s) (partialState inputs)

def hash10 (inputs : Fin 10 → F) : F := (mix M (sbox (suffixState inputs))) 0

end MSP.Poseidon.Optimized
