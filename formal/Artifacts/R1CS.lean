import Spec.Basic

/-!
# Explicit R1CS semantics

This module interprets extracted constraints over `Spec.Basic.F`. It neither
uses `Spec.Relation.R` nor instantiates the opaque declarations in `Spec.Circuit`.
The Python exporter is outside Lean's trusted kernel: byte decoding and signal
projections still need an audited binding, and C1/C1c need separate proofs.
-/

namespace MSP.Artifacts

/-- Wire index and canonical integer coefficient from the binary artifact. -/
abbrev LinearCombination := List (ℕ × ℕ)

structure Constraint where
  a : LinearCombination
  b : LinearCombination
  c : LinearCombination
  deriving Repr

structure System where
  wires : ℕ
  constraints : List Constraint

/-- Values beyond `wires` are irrelevant for a well-formed system. -/
abbrev Assignment := ℕ → F

def LinearCombination.eval (lc : LinearCombination) (w : Assignment) : F :=
  (lc.map fun t => (t.2 : F) * w t.1).sum

def LinearCombination.WellFormed (lc : LinearCombination) (n : ℕ) : Prop :=
  ∀ t ∈ lc, t.1 < n ∧ t.2 < p

def Constraint.Holds (c : Constraint) (w : Assignment) : Prop :=
  c.a.eval w * c.b.eval w = c.c.eval w

def System.WellFormed (s : System) : Prop :=
  0 < s.wires ∧ ∀ c ∈ s.constraints,
    c.a.WellFormed s.wires ∧ c.b.WellFormed s.wires ∧ c.c.WellFormed s.wires

/-- Exactly `wire 0 = 1` and `A(w) * B(w) = C(w)` for every constraint. -/
def System.Satisfied (s : System) (w : Assignment) : Prop :=
  w 0 = 1 ∧ ∀ c ∈ s.constraints, c.Holds w

theorem System.constant_one {s : System} {w : Assignment} (h : s.Satisfied w) :
    w 0 = 1 := h.1

theorem System.constraint_holds {s : System} {w : Assignment} (h : s.Satisfied w)
    {c : Constraint} (hc : c ∈ s.constraints) : c.Holds w := h.2 c hc

/-- The representation cannot constrain hidden wires beyond the declared count. -/
theorem LinearCombination.eval_congr {lc : LinearCombination} {n : ℕ}
    (h : lc.WellFormed n) {u v : Assignment} (eqv : ∀ i < n, u i = v i) :
    lc.eval u = lc.eval v := by
  unfold eval
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [eqv t.1 (h t ht).1]

theorem System.satisfied_congr {s : System} (hs : s.WellFormed)
    {u v : Assignment} (eqv : ∀ i < s.wires, u i = v i) :
    s.Satisfied u ↔ s.Satisfied v := by
  unfold Satisfied
  rw [eqv 0 hs.1]
  have eqc : ∀ c ∈ s.constraints, c.Holds u ↔ c.Holds v := by
    intro c hc
    obtain ⟨ha, hb, hc'⟩ := hs.2 c hc
    unfold Constraint.Holds
    rw [LinearCombination.eval_congr ha eqv, LinearCombination.eval_congr hb eqv,
        LinearCombination.eval_congr hc' eqv]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun c hc => (eqc c hc).mp (h c hc)⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun c hc => (eqc c hc).mpr (h c hc)⟩

end MSP.Artifacts
