import Artifacts.Compression
import Artifacts.Spend

/-!
# Compression from the complete pinned R1CS

The generated `Spend.system` contains every constraint in the pinned binary.
The proof below discharges prefix containment in Lean; the binary decoder and
byte-for-byte generation check remain external parts of artifact provenance.
-/

namespace MSP.Artifacts.FullCompression

/-- Definitional equality checks every coefficient in the nine-constraint prefix. -/
theorem compression_prefix_eq :
    CompressionData.constraints = (Spend.chunk0 ++ Spend.chunk1).take 9 := rfl

private theorem first_chunks_mem {c : Constraint}
    (hc : c ∈ Spend.chunk0 ++ Spend.chunk1) : c ∈ Spend.constraints := by
  apply List.mem_flatten.mpr
  refine ⟨Spend.group0, by simp, ?_⟩
  apply List.mem_flatten.mpr
  rcases List.mem_append.mp hc with hc | hc
  · exact ⟨Spend.chunk0, by simp, hc⟩
  · exact ⟨Spend.chunk1, by simp, hc⟩

/-- The exact extracted compression prefix belongs to the full generated list. -/
theorem compression_constraints_mem {c : Constraint}
    (hc : c ∈ CompressionData.constraints) : c ∈ Spend.system.constraints := by
  rw [compression_prefix_eq] at hc
  exact first_chunks_mem (List.mem_of_mem_take hc)

/-- Every satisfying assignment of the complete pinned R1CS has the canonical
polynomial gamma under the concrete partial statement projection. Beta is
`PublicSignals.beta_of_pinned_r1cs`. -/
theorem gamma_of_pinned_r1cs (w : Assignment) (h : Spend.system.Satisfied w) :
    w 2 = MSP.γ (Compression.statement w) (w 3 + w 1) :=
  Compression.gamma_of_system w (fun _ hc => compression_constraints_mem hc) h

end MSP.Artifacts.FullCompression
