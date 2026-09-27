import Artifacts.ConstraintCoverage
import Artifacts.AssignmentAssembly

/-! Exact physical layout of the 59 independently assembled circuit parts.
Generated from assignment plan SHA-256 `73eeee9fcb7b6651c1df319d019592f9e0dd5c35d9a5d4941539dd40b065fc7a`.
All write intervals include both retained powers and recovered affine outputs. -/

namespace MSP.Artifacts.CircuitAssemblyLayout

/-- Canonical shared source, selector, path-state and hash-output wires. -/
def boundary (wire : ℕ) : Prop :=
  wire < 103 ∨ (730 ≤ wire ∧ wire < 792) ∨ (7060 ≤ wire ∧ wire < 7122) ∨
  wire = 1031 ∨ wire = 1032 ∨ wire = 7361 ∨ wire = 7362 ∨ wire = 6309 ∨ wire = 12639

instance (wire : ℕ) : Decidable (boundary wire) := by unfold boundary; infer_instance

def spanData : Vector (List (ℕ × ℕ)) 59 :=
  ⟨#[[(1, 2), (111, 569)],
    [(791, 1031)],
    [(1031, 1032), (1033, 1272)],
    [(770, 771), (1272, 1529)],
    [(771, 772), (1529, 1768)],
    [(772, 773), (1768, 2007)],
    [(773, 774), (2007, 2246)],
    [(774, 775), (2246, 2485)],
    [(775, 776), (2485, 2724)],
    [(776, 777), (2724, 2963)],
    [(777, 778), (2963, 3202)],
    [(778, 779), (3202, 3441)],
    [(779, 780), (3441, 3680)],
    [(780, 781), (3680, 3919)],
    [(781, 782), (3919, 4158)],
    [(782, 783), (4158, 4397)],
    [(783, 784), (4397, 4636)],
    [(784, 785), (4636, 4875)],
    [(785, 786), (4875, 5114)],
    [(786, 787), (5114, 5353)],
    [(787, 788), (5353, 5592)],
    [(788, 789), (5592, 5831)],
    [(789, 790), (5831, 6070)],
    [(790, 791), (6070, 6309)],
    [(99, 100), (6310, 6567)],
    [(6309, 6310), (6567, 6806)],
    [(1032, 1033), (6806, 7060)],
    [(7121, 7361)],
    [(7361, 7362), (7363, 7602)],
    [(7100, 7101), (7602, 7859)],
    [(7101, 7102), (7859, 8098)],
    [(7102, 7103), (8098, 8337)],
    [(7103, 7104), (8337, 8576)],
    [(7104, 7105), (8576, 8815)],
    [(7105, 7106), (8815, 9054)],
    [(7106, 7107), (9054, 9293)],
    [(7107, 7108), (9293, 9532)],
    [(7108, 7109), (9532, 9771)],
    [(7109, 7110), (9771, 10010)],
    [(7110, 7111), (10010, 10249)],
    [(7111, 7112), (10249, 10488)],
    [(7112, 7113), (10488, 10727)],
    [(7113, 7114), (10727, 10966)],
    [(7114, 7115), (10966, 11205)],
    [(7115, 7116), (11205, 11444)],
    [(7116, 7117), (11444, 11683)],
    [(7117, 7118), (11683, 11922)],
    [(7118, 7119), (11922, 12161)],
    [(7119, 7120), (12161, 12400)],
    [(7120, 7121), (12400, 12639)],
    [(100, 101), (12640, 12897)],
    [(12639, 12640), (12897, 13136)],
    [(7362, 7363), (13136, 13390)],
    [(101, 102), (13390, 13647)],
    [(102, 103), (13647, 13904)],
    [(569, 728), (13918, 14839)],
    [(728, 730), (13904, 13918), (14839, 14842)],
    [(103, 111)],
    []], rfl⟩

def spans (i : Fin 59) : List (ℕ × ℕ) := spanData.get i

def writes (i : Fin 59) (wire : ℕ) : Prop :=
  ∃ span ∈ spans i, span.1 ≤ wire ∧ wire < span.2

instance (i : Fin 59) (wire : ℕ) : Decidable (writes i wire) := by
  unfold writes
  infer_instance

def smallPart (i : Fin 54) : Fin 59 := ⟨i.val + 1, by omega⟩

def familyData : Vector ConstraintCoverage.Family 59 :=
  ⟨#[.beta, .small 0, .small 1, .small 2, .small 3, .small 4, .small 5, .small 6, .small 7, .small 8, .small 9, .small 10, .small 11, .small 12, .small 13, .small 14, .small 15, .small 16, .small 17, .small 18, .small 19, .small 20, .small 21, .small 22, .small 23, .small 24, .small 25, .small 26, .small 27, .small 28, .small 29, .small 30, .small 31, .small 32, .small 33, .small 34, .small 35, .small 36, .small 37, .small 38, .small 39, .small 40, .small 41, .small 42, .small 43, .small 44, .small 45, .small 46, .small 47, .small 48, .small 49, .small 50, .small 51, .small 52, .small 53, .ranges, .controls, .gamma, .paths], rfl⟩

def constraints (i : Fin 59) : List Constraint := (familyData.get i).constraints

def outputData : Vector ℕ 55 := ⟨#[1, 791, 1031, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 99, 6309, 1032, 7121, 7361, 7100, 7101, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117, 7118, 7119, 7120, 100, 12639, 7362, 101, 102], rfl⟩
def outputWire (i : Fin 55) : ℕ := outputData.get i

theorem constraints_small (i : Fin 54) :
    constraints (smallPart i) = (SmallHashGatesData.gate i).constraints := by
  fin_cases i <;> rfl

theorem source_boundary (wire : ℕ) (h : wire < 103) : boundary wire := Or.inl h

end MSP.Artifacts.CircuitAssemblyLayout
