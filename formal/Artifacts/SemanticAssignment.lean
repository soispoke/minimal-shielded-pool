import Artifacts.BaseAssignment
import Artifacts.PathCompletenessGates

/-! A canonical shared boundary for the completeness construction. Source and
public wires come from the relation witness; auxiliary interfaces contain the
ordinary reference hashes and the explicit Merkle trace. The path bit/selector
fragment is then constructed independently of every hash-gadget witness. -/

namespace MSP.Artifacts.SemanticAssignment

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def pkWire (k : Fin 2) : ℕ := 1032 + 6330 * k.val
def innerWire (k : Fin 2) : ℕ := 1031 + 6330 * k.val
def domainWire (k : Fin 2) : ℕ := 791 + 6330 * k.val
def occurrenceWire (k : Fin 2) : ℕ := 6309 + 6330 * k.val

def semantic (x : Statement) (w : MSP.Witness) (al : F) : Assignment := fun wire =>
  if wire < 103 then BaseAssignment.build x w al wire else
  match wire with
  | 1032 => MSP.pk (w.sk 0)
  | 7362 => MSP.pk (w.sk 1)
  | 1031 => MSP.inner (w.sk 0) (w.ρ 0)
  | 7361 => MSP.inner (w.sk 1) (w.ρ 1)
  | 791 => MSP.nfKey x.d (w.sk 0)
  | 7121 => MSP.nfKey x.d (w.sk 1)
  | 6309 => H2 (w.leaf 0) (w.idx 0 : F)
  | 12639 => H2 (w.leaf 1) (w.idx 1 : F)
  | _ =>
    if 770 ≤ wire ∧ wire ≤ 790 then
      PathCompleteness.trace (w.leaf 0) (w.idx 0) (w.sib 0) (wire - 770) else
    if 7100 ≤ wire ∧ wire ≤ 7120 then
      PathCompleteness.trace (w.leaf 1) (w.idx 1) (w.sib 1) (wire - 7100) else 0

def build (x : Statement) (w : MSP.Witness) (al : F) : Assignment :=
  PathCompleteness.complete (semantic x w al) w.idx

theorem semantic_source (x : Statement) (w : MSP.Witness) (al : F)
    (i : ℕ) (hi : i < 103) : semantic x w al i = BaseAssignment.build x w al i := by
  simp only [semantic, hi, ↓reduceIte]

/-- Canonical path bits agree with the source witness's existing digits. -/
theorem source_agreement (x : Statement) (w : MSP.Witness) (al : F)
    (i : ℕ) (hi : i < 103) : build x w al i = BaseAssignment.build x w al i := by
  interval_cases i <;> rfl

@[simp] theorem constant (x : Statement) (w : MSP.Witness) (al : F) :
    build x w al 0 = 1 := rfl

theorem semantic_cur (x : Statement) (w : MSP.Witness) (al : F)
    (k : Fin 2) (n : ℕ) (hn : n ≤ DEPTH) :
    semantic x w al (PathGatesData.curStart k + n) =
      PathCompleteness.trace (w.leaf k) (w.idx k) (w.sib k) n := by
  change n ≤ 20 at hn
  fin_cases k <;> interval_cases n <;> rfl

theorem semantic_sibling (x : Statement) (w : MSP.Witness) (al : F)
    (k : Fin 2) (l : Fin DEPTH) :
    semantic x w al (PathBitsData.siblingWire k l) = w.sib k l := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;> rfl

@[simp] theorem cur (x : Statement) (w : MSP.Witness) (al : F)
    (k : Fin 2) (n : ℕ) (hn : n ≤ DEPTH) :
    build x w al (PathGatesData.curStart k + n) =
      PathCompleteness.trace (w.leaf k) (w.idx k) (w.sib k) n := by
  rw [build, PathCompleteness.complete_cur _ _ k n hn, semantic_cur _ _ _ k n hn]

theorem leaf (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (PathGatesData.curStart k) = w.leaf k := by
  simpa only [Nat.add_zero, PathCompleteness.trace_zero] using cur x w al k 0 (by omega)

@[simp] theorem pk_value (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (pkWire k) = MSP.pk (w.sk k) := by fin_cases k <;> rfl

@[simp] theorem inner_value (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (innerWire k) = MSP.inner (w.sk k) (w.ρ k) := by fin_cases k <;> rfl

@[simp] theorem domain_value (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (domainWire k) = MSP.nfKey x.d (w.sk k) := by fin_cases k <;> rfl

@[simp] theorem occurrence_value (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    build x w al (occurrenceWire k) = H2 (w.leaf k) (w.idx k : F) := by fin_cases k <;> rfl

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

theorem projections (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w) :
    ConcreteWitness.statementOf (build x w al) = x ∧
      ConcreteWitness.ofAssignment (build x w al) = w ∧
      ConcreteWitness.publicOf (build x w al) = (β x, γ x (al + β x), al) :=
  BaseAssignment.projections_of_agreement _ x w al h (source_agreement x w al)

theorem path_complete (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w) :
    (∀ k, PathBits.index (build x w al) k = w.idx k) ∧
    (∀ c ∈ PathCompleteness.constraints, c.Holds (build x w al)) ∧
    (∀ k, PathGates.NodeHashes (build x w al) k) := by
  apply PathCompleteness.complete_path (semantic x w al) w.idx w.leaf w.sib rfl h.1
    (semantic_cur x w al) (semantic_sibling x w al)
  intro k hv
  have hv' : w.v k ≠ 0 := by
    fin_cases k <;> exact hv
  exact h.2.2.2.1 k hv'

end MSP.Artifacts.SemanticAssignment
