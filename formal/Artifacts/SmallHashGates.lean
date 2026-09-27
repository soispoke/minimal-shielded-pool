import Artifacts.SmallHashGatesCertificates

/-!
# All retained small-hash S-boxes of the pinned R1CS

There are 4,366 retained x⁵ gates in the 54 note, path and output hash instances.
The theorems below prove their nonlinear equations directly from the full system.
They also expose complete full/partial-stage interfaces, including source-fixed
coordinates folded by the compiler. The remaining affine certificates must bind
these stages and the recorded interface forms to Optimized3/Optimized4 hashes.
-/

namespace MSP.Artifacts.SmallHashGates

open BetaGates SmallHashGatesData

/-- Every retained S-box in all 54 instances has its actual fifth-power relation. -/
theorem sigma_of_system (w : Assignment) (h : Spend.system.Satisfied w)
    (i : Fin 54) (t : Fin (gate i).tripleCount) :
    eval (output (gate i) t) w = (eval (input (gate i) t) w)^5 :=
  sigma_of_signs (gate i) t (SmallHashGatesCertificates.signs i t) w h

/-- Input to an actual full-round S-box, or its explicit source-fixed initial coordinate. -/
def fullInputForm (g : Instance) (initialConstants : Fin (g.arity + 1) → F)
    (r : Fin 8) (j : Fin (g.arity + 1)) : Form :=
  match g.fullStage r j with
  | some t => input g t
  | none => constant ((g.foldedInput j).getD 0 + initialConstants j)

def fullOutputForm (g : Instance) (initialConstants : Fin (g.arity + 1) → F)
    (r : Fin 8) (j : Fin (g.arity + 1)) : Form :=
  match g.fullStage r j with
  | some t => output g t
  | none => constant (((g.foldedInput j).getD 0 + initialConstants j)^5)

def partialInputForm (g : Instance) (r : Fin g.partialRounds) : Form := input g (g.partialStage r)
def partialOutputForm (g : Instance) (r : Fin g.partialRounds) : Form := output g (g.partialStage r)

/-- Complete full-round nonlinear interface. The caller supplies the optimized
schedule's initial constants; actual affine binding remains a separate check. -/
theorem full_stage_sbox (w : Assignment) (h : Spend.system.Satisfied w) (i : Fin 54)
    (initialConstants : Fin ((gate i).arity + 1) → F)
    (r : Fin 8) (j : Fin ((gate i).arity + 1)) :
    eval (fullOutputForm (gate i) initialConstants r j) w =
      (eval (fullInputForm (gate i) initialConstants r j) w)^5 := by
  cases hs : (gate i).fullStage r j with
  | none => simpa only [fullInputForm, fullOutputForm, hs] using
      folded_sbox (((gate i).foldedInput j).getD 0 + initialConstants j) w h.1
  | some t => simpa only [fullInputForm, fullOutputForm, hs] using sigma_of_system w h i t

/-- Complete partial-round nonlinear interface on the actual retained stage indices. -/
theorem partial_stage_sbox (w : Assignment) (h : Spend.system.Satisfied w) (i : Fin 54)
    (r : Fin (gate i).partialRounds) :
    eval (partialOutputForm (gate i) r) w = (eval (partialInputForm (gate i) r) w)^5 :=
  sigma_of_system w h i ((gate i).partialStage r)

#print axioms sigma_of_system
#print axioms full_stage_sbox
#print axioms partial_stage_sbox

end MSP.Artifacts.SmallHashGates
