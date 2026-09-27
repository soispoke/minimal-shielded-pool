import Artifacts.BetaGatesData
import Artifacts.SmallHashGatesData
import Artifacts.ControlCompleteness
import Artifacts.PathCompletenessGates
import Artifacts.RangeAssignmentCompleteness

/-! Slice bookkeeping for complete coverage. The concrete coverage certificates
are separate, so these generic lemmas assert no artifact-specific coverage. -/

namespace MSP.Artifacts.ConstraintCoverage

inductive Family where
  | gamma
  | beta
  | small (index : Fin 54)
  | ranges
  | controls
  | paths

def Family.constraints : Family → List Constraint
  | .gamma => CompressionData.constraints
  | .beta => BetaGatesData.constraints
  | .small i => (SmallHashGatesData.gate i).constraints
  | .ranges => RangeAssignmentCompleteness.constraints
  | .controls => ControlCompleteness.constraints
  | .paths => PathCompleteness.constraints

/-- One contiguous piece of an already proved fragment. -/
structure Piece where
  family : Family
  offset : ℕ
  count : ℕ

def Piece.constraints (piece : Piece) : List Constraint :=
  (piece.family.constraints.drop piece.offset).take piece.count

def expand (pieces : List Piece) : List Constraint :=
  (pieces.map Piece.constraints).flatten

theorem mem_family {piece : Piece} {c : Constraint} (hc : c ∈ piece.constraints) :
    c ∈ piece.family.constraints :=
  List.mem_of_mem_drop (List.mem_of_mem_take hc)

theorem expand_covered {pieces : List Piece} {c : Constraint} (hc : c ∈ expand pieces) :
    ∃ family : Family, c ∈ family.constraints := by
  obtain ⟨slice, hs, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨piece, _, rfl⟩ := List.mem_map.mp hs
  exact ⟨piece.family, mem_family hc⟩

end MSP.Artifacts.ConstraintCoverage
