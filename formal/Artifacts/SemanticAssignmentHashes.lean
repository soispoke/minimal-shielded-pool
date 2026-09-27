import Artifacts.SemanticAssignment
import Artifacts.SmallHashGatesInterface

/-! The shared semantic assignment satisfies each extracted hash interface
directly from its definitions and R. This permits the independent physical
hash witnesses to preserve their shared output wire when merged. -/

namespace MSP.Artifacts.SemanticAssignment

open SmallHashGates SmallHashGatesData

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def domainIndex (k : Fin 2) : Fin 54 := ⟨26 * k.val, by omega⟩
def innerIndex (k : Fin 2) : Fin 54 := ⟨1 + 26 * k.val, by omega⟩
def leafIndex (k : Fin 2) : Fin 54 := ⟨2 + 26 * k.val, by omega⟩
def nodeIndex (k : Fin 2) (l : Fin DEPTH) : Fin 54 :=
  ⟨3 + 26 * k.val + l.val, by have := l.isLt; unfold DEPTH at this; omega⟩
def nullIndex (k : Fin 2) : Fin 54 := ⟨23 + 26 * k.val, by omega⟩
def occurrenceIndex (k : Fin 2) : Fin 54 := ⟨24 + 26 * k.val, by omega⟩
def pkIndex (k : Fin 2) : Fin 54 := ⟨25 + 26 * k.val, by omega⟩
def outputIndex (k : Fin 2) : Fin 54 := ⟨52 + k.val, by omega⟩

private theorem pk_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (pkIndex k) =
      (BetaGates.eval [(pkWire k, 1)] a = H3 (BetaGates.eval [(0, 1)] a)
        (BetaGates.eval [(PathBitsData.skWire k, 1)] a) (BetaGates.eval [] a)) := by
  fin_cases k <;> rfl

private theorem inner_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (innerIndex k) =
      (BetaGates.eval [(innerWire k, 1)] a = H2 (BetaGates.eval [(pkWire k, 1)] a)
        (BetaGates.eval [(PathBitsData.rhoWire k, 1)] a)) := by
  fin_cases k <;> rfl

private theorem leaf_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (leafIndex k) =
      (BetaGates.eval [(PathGatesData.curStart k, 1)] a = H3 (BetaGates.eval [(0, 2)] a)
        (BetaGates.eval [(innerWire k, 1)] a)
        (BetaGates.eval [(PathBitsData.valueWire k, 1)] a)) := by
  fin_cases k <;> rfl

private theorem domain_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (domainIndex k) =
      (BetaGates.eval [(domainWire k, 1)] a = H2 (BetaGates.eval [(5, 1)] a)
        (BetaGates.eval [(PathBitsData.skWire k, 1)] a)) := by
  fin_cases k <;> rfl

private theorem occurrence_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (occurrenceIndex k) =
      (BetaGates.eval [(occurrenceWire k, 1)] a =
        H2 (BetaGates.eval [(PathGatesData.curStart k, 1)] a)
          (BetaGates.eval (BetaGates.ofLC
            (RangeLemmas.weightedWires (PathBitsData.bitStart k) DEPTH)) a)) := by
  fin_cases k <;> rfl

private theorem nullifier_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (nullIndex k) =
      (BetaGates.eval [(99 + k.val, 1)] a = H3 (BetaGates.eval [(0, 4)] a)
        (BetaGates.eval [(domainWire k, 1)] a)
        (BetaGates.eval [(occurrenceWire k, 1)] a)) := by
  fin_cases k <;> rfl

private theorem output_interface (a : Assignment) (k : Fin 2) :
    HashBinding a (outputIndex k) =
      (BetaGates.eval [(101 + k.val, 1)] a = H3 (BetaGates.eval [(0, 2)] a)
        (BetaGates.eval [(PathBitsData.outputInnerWire k, 1)] a)
        (BetaGates.eval [(PathBitsData.outputValueWire k, 1)] a)) := by
  fin_cases k <;> rfl

private theorem node_interface (a : Assignment) (k : Fin 2) (l : Fin DEPTH) :
    HashBinding a (nodeIndex k l) =
      (BetaGates.eval [(PathGatesData.curStart k + (l.val + 1), 1)] a =
        H2 (BetaGates.eval [(PathGatesData.leftStart k + l.val, 1)] a)
          (BetaGates.eval [(PathGatesData.rightStart k + l.val, 1)] a)) := by
  change Fin 20 at l
  fin_cases k <;> fin_cases l <;> rfl

theorem pk_binding (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    HashBinding (build x w al) (pkIndex k) := by
  rw [pk_interface]
  simp [BetaGates.eval, MSP.pk]

theorem inner_binding (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    HashBinding (build x w al) (innerIndex k) := by
  rw [inner_interface]
  simp [BetaGates.eval, MSP.inner]

theorem leaf_binding (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    HashBinding (build x w al) (leafIndex k) := by
  rw [leaf_interface]
  simp [BetaGates.eval, leaf, MSP.Witness.leaf, MSP.cm]

theorem domain_binding (x : Statement) (w : MSP.Witness) (al : F) (k : Fin 2) :
    HashBinding (build x w al) (domainIndex k) := by
  rw [domain_interface]
  have hd : build x w al 5 = x.d := rfl
  simp [BetaGates.eval, hd, MSP.nfKey]

theorem occurrence_binding (x : Statement) (w : MSP.Witness) (al : F)
    (h : MSP.R x w) (k : Fin 2) :
    HashBinding (build x w al) (occurrenceIndex k) := by
  rw [occurrence_interface, BetaGates.eval_ofLC, ← PathBits.index_cast,
    (path_complete x w al h).1 k]
  simp [BetaGates.eval, leaf]

theorem nullifier_binding (x : Statement) (w : MSP.Witness) (al : F)
    (h : MSP.R x w) (k : Fin 2) :
    HashBinding (build x w al) (nullIndex k) := by
  rw [nullifier_interface]
  have hn : build x w al (99 + k.val) = MSP.nf x.d (w.sk k) (w.leaf k) (w.idx k) := by
    fin_cases k
    · exact h.2.1
    · exact h.2.2.1
  simpa only [BetaGates.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero, constant, mul_one, domain_value, occurrence_value, MSP.nf] using hn

theorem output_binding (x : Statement) (w : MSP.Witness) (al : F)
    (h : MSP.R x w) (k : Fin 2) :
    HashBinding (build x w al) (outputIndex k) := by
  rw [output_interface]
  have ho : build x w al (101 + k.val) = MSP.cm (w.oi k) (w.ov k) := by
    fin_cases k
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2.1
  simpa only [BetaGates.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero, constant, mul_one, output_inner, output_value, MSP.cm] using ho

theorem node_binding (x : Statement) (w : MSP.Witness) (al : F)
    (h : MSP.R x w) (k : Fin 2) (l : Fin DEPTH) :
    HashBinding (build x w al) (nodeIndex k l) := by
  rw [node_interface]
  simpa [BetaGates.eval] using (path_complete x w al h).2.2 k l

/-- All actual hash interfaces on the canonical shared boundary, from R alone. -/
theorem hash_bindings (x : Statement) (w : MSP.Witness) (al : F) (h : MSP.R x w) :
    ∀ i : Fin 54, HashBinding (build x w al) i := by
  intro i
  fin_cases i
  · exact domain_binding x w al 0
  · exact inner_binding x w al 0
  · exact leaf_binding x w al 0
  · exact node_binding x w al h 0 ⟨0, by decide⟩
  · exact node_binding x w al h 0 ⟨1, by decide⟩
  · exact node_binding x w al h 0 ⟨2, by decide⟩
  · exact node_binding x w al h 0 ⟨3, by decide⟩
  · exact node_binding x w al h 0 ⟨4, by decide⟩
  · exact node_binding x w al h 0 ⟨5, by decide⟩
  · exact node_binding x w al h 0 ⟨6, by decide⟩
  · exact node_binding x w al h 0 ⟨7, by decide⟩
  · exact node_binding x w al h 0 ⟨8, by decide⟩
  · exact node_binding x w al h 0 ⟨9, by decide⟩
  · exact node_binding x w al h 0 ⟨10, by decide⟩
  · exact node_binding x w al h 0 ⟨11, by decide⟩
  · exact node_binding x w al h 0 ⟨12, by decide⟩
  · exact node_binding x w al h 0 ⟨13, by decide⟩
  · exact node_binding x w al h 0 ⟨14, by decide⟩
  · exact node_binding x w al h 0 ⟨15, by decide⟩
  · exact node_binding x w al h 0 ⟨16, by decide⟩
  · exact node_binding x w al h 0 ⟨17, by decide⟩
  · exact node_binding x w al h 0 ⟨18, by decide⟩
  · exact node_binding x w al h 0 ⟨19, by decide⟩
  · exact nullifier_binding x w al h 0
  · exact occurrence_binding x w al h 0
  · exact pk_binding x w al 0
  · exact domain_binding x w al 1
  · exact inner_binding x w al 1
  · exact leaf_binding x w al 1
  · exact node_binding x w al h 1 ⟨0, by decide⟩
  · exact node_binding x w al h 1 ⟨1, by decide⟩
  · exact node_binding x w al h 1 ⟨2, by decide⟩
  · exact node_binding x w al h 1 ⟨3, by decide⟩
  · exact node_binding x w al h 1 ⟨4, by decide⟩
  · exact node_binding x w al h 1 ⟨5, by decide⟩
  · exact node_binding x w al h 1 ⟨6, by decide⟩
  · exact node_binding x w al h 1 ⟨7, by decide⟩
  · exact node_binding x w al h 1 ⟨8, by decide⟩
  · exact node_binding x w al h 1 ⟨9, by decide⟩
  · exact node_binding x w al h 1 ⟨10, by decide⟩
  · exact node_binding x w al h 1 ⟨11, by decide⟩
  · exact node_binding x w al h 1 ⟨12, by decide⟩
  · exact node_binding x w al h 1 ⟨13, by decide⟩
  · exact node_binding x w al h 1 ⟨14, by decide⟩
  · exact node_binding x w al h 1 ⟨15, by decide⟩
  · exact node_binding x w al h 1 ⟨16, by decide⟩
  · exact node_binding x w al h 1 ⟨17, by decide⟩
  · exact node_binding x w al h 1 ⟨18, by decide⟩
  · exact node_binding x w al h 1 ⟨19, by decide⟩
  · exact nullifier_binding x w al h 1
  · exact occurrence_binding x w al h 1
  · exact pk_binding x w al 1
  · exact output_binding x w al h 0
  · exact output_binding x w al h 1

end MSP.Artifacts.SemanticAssignment
