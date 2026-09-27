import Artifacts.CircuitSoundness
import Artifacts.CircuitCompleteness
import Proofs.Effects
import Proofs.C6
import Proofs.Composes

/-! Close the circuit/model side of the canonical main theorem. The remaining
arguments below are exactly the undischarged concrete chain obligations. -/
namespace MSP

theorem circuit_model : C1 ∧ C1c ∧ ModelTheorem := ⟨c1, c1c, model_theorem⟩

theorem main_theorem_of_chain (h2 : C2) (h2c : C2c) (h8 : C8)
    (h9 : C9) (h10 : C10) (href : Refines) : MainTheorem :=
  ⟨c1, c1c, model_theorem, h2, h2c, c6, h8, h9, h10, href⟩

theorem chain_corollary_of_chain (h2 : C2) (h2c : C2c) (h8 : C8)
    (h9 : C9) (h10 : C10) (href : Refines) : ChainCorollary :=
  composes (main_theorem_of_chain h2 h2c h8 h9 h10 href)

#print axioms circuit_model
#print axioms chain_corollary_of_chain
end MSP
