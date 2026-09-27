import Artifacts.SmallHashGatesInterface
import Artifacts.RelationFragments

/-!
# Canonical notes from the 54 pinned hash interfaces

This assembly consumes the individual H2/H3 equations on the exact extracted
instance forms. It derives the note, nullifier, path and output claims without
assuming R, a whole Merkle-root equation, or a high-level nullifier equation.
The instance hash equations are premises here; `SmallHashGatesComplete`
proves them and `CircuitSoundness` discharges them.
-/

namespace MSP.Artifacts.NoteBindings

open SmallHashGates SmallHashGatesData ConcreteWitness

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private def domainIndex (k : Fin 2) : Fin 54 := ⟨26 * k.val, by omega⟩
private def innerIndex (k : Fin 2) : Fin 54 := ⟨1 + 26 * k.val, by omega⟩
private def leafIndex (k : Fin 2) : Fin 54 := ⟨2 + 26 * k.val, by omega⟩
private def nodeIndex (k : Fin 2) (l : Fin DEPTH) : Fin 54 :=
  ⟨3 + 26 * k.val + l.val, by have := l.isLt; unfold DEPTH at this; omega⟩
private def nullIndex (k : Fin 2) : Fin 54 := ⟨23 + 26 * k.val, by omega⟩
private def occurrenceIndex (k : Fin 2) : Fin 54 := ⟨24 + 26 * k.val, by omega⟩
private def pkIndex (k : Fin 2) : Fin 54 := ⟨25 + 26 * k.val, by omega⟩
private def outputIndex (k : Fin 2) : Fin 54 := ⟨52 + k.val, by omega⟩

private def pkWire (k : Fin 2) : ℕ := 1032 + 6330 * k.val
private def innerWire (k : Fin 2) : ℕ := 1031 + 6330 * k.val
private def domainWire (k : Fin 2) : ℕ := 791 + 6330 * k.val
private def occurrenceWire (k : Fin 2) : ℕ := 6309 + 6330 * k.val

/- These equalities are kernel-checked projections of the generated records.
They keep the large round data out of the subsequent symbolic reasoning. -/
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

/-- The first key hash, including the explicit domain tag and final zero. -/
theorem pk_binding (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (pkWire k) = MSP.pk ((ofAssignment a).sk k) := by
  have hc := hashes (pkIndex k)
  rw [pk_interface] at hc
  simpa [BetaGates.eval, h.1, MSP.pk, ofAssignment] using hc

/-- The note inner commits to the exact private key and rho signals. -/
theorem inner_binding (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (innerWire k) = MSP.inner ((ofAssignment a).sk k) ((ofAssignment a).ρ k) := by
  unfold MSP.inner
  rw [← pk_binding a h hashes k]
  have hc := hashes (innerIndex k)
  rw [inner_interface] at hc
  simpa [BetaGates.eval, ofAssignment] using hc

/-- Each retained initial path-state wire is its canonical input commitment. -/
theorem leaf_binding (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (PathGatesData.curStart k) = (ofAssignment a).leaf k := by
  unfold Witness.leaf MSP.cm
  rw [← inner_binding a h hashes k]
  have hc := hashes (leafIndex k)
  rw [leaf_interface] at hc
  simpa [BetaGates.eval, h.1, ofAssignment] using hc

/-- The nullifier key uses the exact statement domain and private spend key. -/
theorem domain_key_binding (a : Assignment)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (domainWire k) = MSP.nfKey (statementOf a).d ((ofAssignment a).sk k) := by
  have hc := hashes (domainIndex k)
  rw [domain_interface] at hc
  simpa [BetaGates.eval, MSP.nfKey, statementOf, Compression.statement, ofAssignment] using hc

/-- The occurrence hash uses the canonical natural index, through its field cast. -/
theorem occurrence_binding (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (occurrenceWire k) = H2 ((ofAssignment a).leaf k) ((ofAssignment a).idx k : F) := by
  have hc := hashes (occurrenceIndex k)
  rw [occurrence_interface, BetaGates.eval_ofLC, ← ConcreteWitness.index_cast] at hc
  rw [← leaf_binding a h hashes k]
  simpa [BetaGates.eval] using hc

/-- Both nullifiers include the statement domain, leaf commitment and exact index. -/
theorem nullifier_binding (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (99 + k.val) = MSP.nf (statementOf a).d ((ofAssignment a).sk k)
      ((ofAssignment a).leaf k) ((ofAssignment a).idx k) := by
  unfold MSP.nf
  rw [← domain_key_binding a hashes k, ← occurrence_binding a h hashes k]
  have hc := hashes (nullIndex k)
  rw [nullifier_interface] at hc
  simpa [BetaGates.eval, h.1] using hc

/-- The output commitment instances use the exact private inner/value signals. -/
theorem output_binding (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) (k : Fin 2) :
    a (101 + k.val) = MSP.cm ((ofAssignment a).oi k) ((ofAssignment a).ov k) := by
  have hc := hashes (outputIndex k)
  rw [output_interface] at hc
  simpa [BetaGates.eval, h.1, MSP.cm, ofAssignment] using hc

/-- All forty node interfaces are precisely the concrete path-gate hash premises. -/
theorem node_bindings (a : Assignment) (hashes : ∀ i, HashBinding a i) :
    ∀ k, PathGates.NodeHashes a k := by
  intro k l
  have hc := hashes (nodeIndex k l)
  rw [node_interface] at hc
  simpa [BetaGates.eval] using hc

/-- The entire canonical relation, conditional only on the individual extracted
hash-instance equations in addition to full R1CS satisfaction. -/
theorem relation_of_pinned_hash_instances (a : Assignment) (h : Spend.system.Satisfied a)
    (hashes : ∀ i, HashBinding a i) : R (statementOf a) (ofAssignment a) := by
  apply RelationFragments.relation_of_gadget_hashes a h
  · exact nullifier_binding a h hashes 0
  · exact nullifier_binding a h hashes 1
  · exact leaf_binding a h hashes
  · exact node_bindings a hashes
  · exact output_binding a h hashes 0
  · exact output_binding a h hashes 1

end MSP.Artifacts.NoteBindings
