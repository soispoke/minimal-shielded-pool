import Artifacts.PathCompleteness
import Proofs.CircuitArithmetic

/-! Canonical public/source wires for a valid relation witness. This construction
sets only wires 0 through 102; all auxiliary wires start at zero. No claim of
full R1CS satisfaction is made here. -/

namespace MSP.Artifacts.BaseAssignment

open MSP.CircuitCompleteness

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Public values, statement fields, private inputs, and canonical index digits. -/
def build (x : Statement) (w : MSP.Witness) (al : F) : Assignment := fun wire =>
  match wire with
  | 0 => 1
  | 1 => β x
  | 2 => γ x (al + β x)
  | 3 => al
  | 4 => x.root
  | 5 => x.d
  | 6 => w.sk 0
  | 7 => w.sk 1
  | 8 => w.ρ 0
  | 9 => w.ρ 1
  | 10 => w.v 0
  | 11 => w.v 1
  | 92 => w.oi 0
  | 93 => w.oi 1
  | 94 => w.ov 0
  | 95 => w.ov 1
  | 96 => x.pub
  | 97 => x.rcp
  | 98 => x.auth
  | 99 => x.nf1
  | 100 => x.nf2
  | 101 => x.o1
  | 102 => x.o2
  | _ =>
    if h : 12 ≤ wire ∧ wire < 32 then w.sib 0 ⟨wire - 12, by unfold DEPTH; omega⟩ else
    if h : 32 ≤ wire ∧ wire < 52 then w.sib 1 ⟨wire - 32, by unfold DEPTH; omega⟩ else
    if 52 ≤ wire ∧ wire < 72 then bitDigit (w.idx 0) (wire - 52) else
    if 72 ≤ wire ∧ wire < 92 then bitDigit (w.idx 1) (wire - 72) else 0

@[simp] theorem constant (x : Statement) (w : MSP.Witness) (al : F) :
    build x w al 0 = 1 := rfl

@[simp] theorem sk (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (PathBitsData.skWire k) = w.sk k := by fin_cases k <;> rfl

@[simp] theorem rho (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (PathBitsData.rhoWire k) = w.ρ k := by fin_cases k <;> rfl

@[simp] theorem value (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (PathBitsData.valueWire k) = w.v k := by fin_cases k <;> rfl

@[simp] theorem output_inner (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (PathBitsData.outputInnerWire k) = w.oi k := by fin_cases k <;> rfl

@[simp] theorem output_value (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (PathBitsData.outputValueWire k) = w.ov k := by fin_cases k <;> rfl

@[simp] theorem sibling (x : Statement) (w : MSP.Witness) (al : F)
    (k : Fin 2) (l : Fin DEPTH) :
    build x w al (PathBitsData.siblingWire k l) = w.sib k l := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;> rfl

theorem bit (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2)
    (i : ℕ) (hi : i < DEPTH) :
    build x w al (PathBitsData.bitStart k + i) = bitDigit (w.idx k) i := by
  change i < 20 at hi
  fin_cases k <;> interval_cases i <;> rfl

theorem index (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2)
    (hindex : w.idx k < 2^DEPTH) : PathBits.index (build x w al) k = w.idx k :=
  PathCompleteness.index_eq_of_bits (build x w al) k (w.idx k) hindex (bit x w al k)

/-- Natural conservation in R determines the field expression of eliminated fee. -/
theorem eliminated_fee (x : Statement) (w : MSP.Witness) (h : MSP.R x w) :
    w.v 0 + w.v 1 - w.ov 0 - w.ov 1 - x.pub = x.fee := by
  have he := h.2.2.2.2.2.2.2.1
  have hf := congrArg (fun n : ℕ => (n : F)) he
  simp only [Nat.cast_add, ZMod.natCast_zmod_val] at hf
  linear_combination hf

/-- The concrete statement has no unassigned fee wire; it recovers the fee
from the exact canonical integer conservation equation. -/
theorem statementOf (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w) :
    ConcreteWitness.statementOf (build x w al) = x := by
  have hf := eliminated_fee x w h
  cases x
  simp only [ConcreteWitness.statementOf, Compression.statement, build] at hf ⊢
  rw [hf]

/-- All private fields and the reconstructed natural indices are unchanged. -/
theorem ofAssignment (x : Statement) (w : MSP.Witness) (al : F)
    (hindex : ∀ k, w.idx k < 2^DEPTH) :
    ConcreteWitness.ofAssignment (build x w al) = w := by
  have hi : (fun k => PathBits.index (build x w al) k) = w.idx :=
    funext fun k => index x w al k (hindex k)
  unfold ConcreteWitness.ofAssignment
  simp only [sk, rho, value, sibling, output_inner, output_value, hi]

@[simp] theorem publicOf (x : Statement) (w : MSP.Witness) (al : F) :
    ConcreteWitness.publicOf (build x w al) = (β x, γ x (al + β x), al) := rfl

theorem relation (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w) :
    MSP.R (ConcreteWitness.statementOf (build x w al))
      (ConcreteWitness.ofAssignment (build x w al)) := by
  rw [statementOf x w al h, ofAssignment x w al h.1]
  exact h

/-- Agreement on source wires is sufficient to preserve the statement. -/
theorem statementOf_congr (a b : Assignment) (h : ∀ i < 103, a i = b i) :
    ConcreteWitness.statementOf a = ConcreteWitness.statementOf b := by
  simp [ConcreteWitness.statementOf, Compression.statement, h]

/-- Agreement on source wires preserves public values as well. -/
theorem publicOf_congr (a b : Assignment) (h : ∀ i < 103, a i = b i) :
    ConcreteWitness.publicOf a = ConcreteWitness.publicOf b := by
  simp [ConcreteWitness.publicOf, PathBitsData.betaWire, PathBitsData.gammaWire,
    PathBitsData.alphaWire, h]

private theorem index_congr (a b : Assignment) (h : ∀ i < 103, a i = b i) (k : Fin 2) :
    PathBits.index a k = PathBits.index b k := by
  simp only [PathBits.index, PathBits.bits_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hil : i < 20 := List.mem_range.mp hi
  apply h
  fin_cases k <;> dsimp [PathBitsData.bitStart] <;> omega

/-- This also preserves witness indices; it does not rely on field equality
of indices or on an already-satisfied bit gadget. -/
theorem ofAssignment_congr (a b : Assignment) (h : ∀ i < 103, a i = b i) :
    ConcreteWitness.ofAssignment a = ConcreteWitness.ofAssignment b := by
  unfold ConcreteWitness.ofAssignment
  congr 1
  · funext k
    apply h
    fin_cases k <;> decide
  · funext k
    apply h
    fin_cases k <;> decide
  · funext k
    apply h
    fin_cases k <;> decide
  · funext k
    exact index_congr a b h k
  · funext k l
    apply h
    change Fin 20 at l
    fin_cases k <;> fin_cases l <;> decide
  · funext k
    apply h
    fin_cases k <;> decide
  · funext k
    apply h
    fin_cases k <;> decide

/-- Any auxiliary update preserving the source wires preserves all projections. -/
theorem projections_of_agreement (a : Assignment) (x : Statement) (w : MSP.Witness)
    (al : F) (h : MSP.R x w) (hag : ∀ i < 103, a i = build x w al i) :
    ConcreteWitness.statementOf a = x ∧ ConcreteWitness.ofAssignment a = w ∧
      ConcreteWitness.publicOf a = (β x, γ x (al + β x), al) :=
  ⟨(statementOf_congr a _ hag).trans (statementOf x w al h),
    (ofAssignment_congr a _ hag).trans (ofAssignment x w al h.1),
    (publicOf_congr a _ hag).trans (publicOf x w al)⟩

#print axioms statementOf
#print axioms ofAssignment
#print axioms projections_of_agreement

end MSP.Artifacts.BaseAssignment
