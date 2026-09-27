import Artifacts.SmallHashGatesData
import Spec.Hash

/-! Statement-level interface for the 54 pinned small-hash instances.
`HashBinding` is proved for all 54 instances in `SmallHashGatesComplete`.
The note/path assembly consumes it as a premise.
-/

namespace MSP.Artifacts.SmallHashGates

open BetaGates SmallHashGatesData

def inputAt (g : Instance) (j : ℕ) : Form :=
  if hj : j < g.arity then g.inputForms ⟨j, hj⟩ else []

/-- Exact per-instance hash conclusion needed by the note/path/output assembly.
The H2/H3 definitions are the concrete ordinary-reference hashes in `Spec.Hash`. -/
def HashBinding (w : Assignment) (i : Fin 54) : Prop :=
  let g := gate i
  match g.arity with
  | 2 => eval g.outputForm w = H2 (eval (inputAt g 0) w) (eval (inputAt g 1) w)
  | 3 => eval g.outputForm w = H3 (eval (inputAt g 0) w) (eval (inputAt g 1) w)
      (eval (inputAt g 2) w)
  | _ => False

end MSP.Artifacts.SmallHashGates
