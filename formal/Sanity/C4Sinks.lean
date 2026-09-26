import Spec

/-! C4's sink clauses. `SettlePre` needs `o1 ≠ SINK 1` and
`o2 ≠ SINK 0`. From `R` alone (R4, R7) and the absence of an `h3` collision
between the output's commitment query and the hardcoded sink query, both
follow. This checks that R7's `((k.val + 1 : ℕ) : F)` cast and `SINK`'s index
agree, and that the needed queries sit in `witnessQueries` and `traceQueries`. -/

namespace MSP
noncomputable section
open Classical

instance : Fact (1 < p) := ⟨by norm_num [p]⟩

theorem one_ne_two_F : (1 : F) ≠ 2 := by
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_one, show (2 : F) = ((2 : ℕ) : F) by norm_num, ZMod.val_natCast] at this
  norm_num [p] at this

/-- Output 2 is never sink 0 unless `H3 2 (oi 1) (ov 1)` collides with `H3 2 1 0`. -/
theorem o2_ne_sink0 (x : Statement) (w : Witness) (hR : R x w)
    (hnc : ¬ (Query.h3 2 (w.oi 1) (w.ov 1)).collide (Query.h3 2 1 0)) :
    x.o2 ≠ SINK 0 := by
  obtain ⟨-, -, -, -, -, ho2, -, -, -, hR7, -⟩ := hR
  intro h
  have hcm : H3 2 (w.oi 1) (w.ov 1) = H3 2 1 0 := by
    have := ho2.symm.trans h; simpa [SINK, cm] using this
  have heq : (2, w.oi 1, w.ov 1) = ((2 : F), (1 : F), (0 : F)) := by
    by_contra hne; exact hnc ⟨hne, hcm⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, hoi, hov⟩ := heq
  have := (hR7 1).1 hov
  rw [hoi] at this
  exact one_ne_two_F (by simpa using this)

theorem o1_ne_sink1 (x : Statement) (w : Witness) (hR : R x w)
    (hnc : ¬ (Query.h3 2 (w.oi 0) (w.ov 0)).collide (Query.h3 2 2 0)) :
    x.o1 ≠ SINK 1 := by
  obtain ⟨-, -, -, -, ho1, -, -, -, -, hR7, -⟩ := hR
  intro h
  have hcm : H3 2 (w.oi 0) (w.ov 0) = H3 2 2 0 := by
    have := ho1.symm.trans h; simpa [SINK, cm] using this
  have heq : (2, w.oi 0, w.ov 0) = ((2 : F), (2 : F), (0 : F)) := by
    by_contra hne; exact hnc ⟨hne, hcm⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, hoi, hov⟩ := heq
  have := (hR7 0).1 hov
  rw [hoi] at this
  exact one_ne_two_F (by simpa using this.symm)

/-- Both queries are in the run's trace for an approved spend. -/
theorem sink_queries_in_trace (P : Pool) (evs : List Event) (s : PoolState) :
    Query.h3 2 1 0 ∈ traceQueries P evs s ∧ Query.h3 2 2 0 ∈ traceQueries P evs s := by
  simp [traceQueries]

theorem out_queries_in_trace (P : Pool) (tx : FrameTx) (g : ℕ) :
    Query.h3 2 ((witOf (extOf P tx)).oi 1) ((witOf (extOf P tx)).ov 1) ∈ eventQueries P (.spend tx g) ∧
    Query.h3 2 ((witOf (extOf P tx)).oi 0) ((witOf (extOf P tx)).ov 0) ∈ eventQueries P (.spend tx g) := by
  simp [eventQueries, witnessQueries]

end
end MSP

#print axioms MSP.o2_ne_sink0
#print axioms MSP.o1_ne_sink1
#print axioms MSP.out_queries_in_trace
