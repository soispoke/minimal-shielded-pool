import Artifacts.PathBits
import Artifacts.FullCompression
import Spec.Relation

/-!
# Concrete raw witness and public projections

Private wire indices come from the exact reproduced symbol map in PathBitsData.
R1 and the gamma equation are proved below. Other circuit claims and complete
statement/witness binding are separate; `Spec.Circuit`'s opaques are unchanged.
-/

namespace MSP.Artifacts.ConcreteWitness

/-- The canonical private-input fields, with the indices reconstructed from
actual path bits. No witness-generator behavior is assumed. -/
def ofAssignment (w : Assignment) : MSP.Witness where
  sk k := w (PathBitsData.skWire k)
  ρ k := w (PathBitsData.rhoWire k)
  v k := w (PathBitsData.valueWire k)
  idx k := PathBits.index w k
  sib k i := w (PathBitsData.siblingWire k i)
  oi k := w (PathBitsData.outputInnerWire k)
  ov k := w (PathBitsData.outputValueWire k)

/-- The concrete statement projection already checked against compression. -/
def statementOf (w : Assignment) : Statement := Compression.statement w

/-- Public order is extracted from the exact symbol file and matches the
R1CS public-wire header: beta, gamma, alpha. -/
def publicOf (w : Assignment) : F × F × F :=
  (w PathBitsData.betaWire, w PathBitsData.gammaWire, w PathBitsData.alphaWire)

theorem public_wires (w : Assignment) : publicOf w = (w 1, w 2, w 3) := rfl

/-- The R1 conjunct for the concrete witness projection. -/
theorem R1 (w : Assignment) (h : Spend.system.Satisfied w) :
    ∀ k, (ofAssignment w).idx k < 2^DEPTH :=
  PathBits.index_bounded w h

theorem index_cast (w : Assignment) (k : Fin 2) :
    ((ofAssignment w).idx k : F) =
      (RangeLemmas.weightedWires (PathBitsData.bitStart k) DEPTH).eval w :=
  PathBits.index_cast w k

/-- The high-level gamma equation for these concrete public/statement projections.
The beta/Poseidon equality remains a separate obligation. -/
theorem public_gamma (w : Assignment) (h : Spend.system.Satisfied w) :
    (publicOf w).2.1 = MSP.γ (statementOf w) ((publicOf w).2.2 + (publicOf w).1) :=
  FullCompression.gamma_of_pinned_r1cs w h

end MSP.Artifacts.ConcreteWitness
