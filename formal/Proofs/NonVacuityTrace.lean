import Proofs.NonVacuityQueries

/-! Reduce the exact model bad-event checks to compact tree-query support.
This changes only how a prospective W1 fixture is checked; all events,
extractor failures, compression failures, and extra queries remain present. -/

namespace MSP.NonVacuity

/-- `traceQueries` with membership-equivalent compact tree queries. -/
def compactTraceQueries (P : Pool) (evs : List Event) (s : PoolState) : List Query :=
  [Query.h3 2 1 0, .h3 2 2 0] ++
  evs.flatMap (eventQueries P) ++
  s.roots.flatMap (fun w => [Query.keccak (rrEntryMsg w.1 w.2.1 w.2.2),
                             .keccak (rrKeyMsg w.1 (w.2.1 % 8192))]) ++
  (List.range s.E).map (fun e => Query.keccak (finalRootMsg e)) ++
  (List.range (s.E + 1)).flatMap fun e =>
    [Query.dom P.c P.A e, .keccak (addr20 P.A ++ u256 e)] ++
    (List.range ((s.leaves e).length + 1)).flatMap fun n =>
      compactQueries DEPTH ((s.leaves e).take n)

theorem compactTraceQueries_mem (P : Pool) (evs : List Event) (s : PoolState) (q : Query) :
    q ∈ compactTraceQueries P evs s ↔ q ∈ traceQueries P evs s := by
  simp only [compactTraceQueries, traceQueries, List.mem_append, List.mem_flatMap,
    compactQueries_mem]

/-- Exact reduction of all bad-event branches, including cross-collisions
between a tree query, an event query, and a caller-supplied extra query. -/
theorem badEventWith_iff_compact (P : Pool) (evs : List Event) (s : PoolState)
    (extra : List Query) :
    BadEventWith P evs s extra ↔
      (∃ q₁ ∈ compactTraceQueries P evs s ++ extra,
        ∃ q₂ ∈ compactTraceQueries P evs s ++ extra, q₁.collide q₂) ∨
      (∃ q ∈ compactTraceQueries P evs s ++ extra, q.degenerate) ∨
      CompressionBreak P evs ∨ ExtractionFailure P evs := by
  simp only [BadEventWith, List.mem_append, compactTraceQueries_mem]

theorem badEvent_iff_compact (P : Pool) (evs : List Event) (s : PoolState) :
    BadEvent P evs s ↔
      (∃ q₁ ∈ compactTraceQueries P evs s,
        ∃ q₂ ∈ compactTraceQueries P evs s, q₁.collide q₂) ∨
      (∃ q ∈ compactTraceQueries P evs s, q.degenerate) ∨
      CompressionBreak P evs ∨ ExtractionFailure P evs := by
  simpa only [BadEvent, List.append_nil] using badEventWith_iff_compact P evs s []

/-- Every trace includes epoch zero's root-source hash, even with no events. -/
theorem source_query_mem (P : Pool) (evs : List Event) (s : PoolState) :
    Query.keccak (addr20 P.A ++ u256 0) ∈ traceQueries P evs s := by
  unfold traceQueries
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨0, List.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
  apply List.mem_append_left
  simp

/-- A necessary concrete Keccak fact, not a replacement for the remaining
collision, degeneration, extraction, or execution checks. -/
theorem source_nondegenerate_of_noBadEvent (P : Pool) (evs : List Event) (s : PoolState)
    (h : ¬ BadEvent P evs s) : 2^64 ≤ K (addr20 P.A ++ u256 0) := by
  by_contra hn
  apply h
  unfold BadEvent BadEventWith
  right
  left
  refine ⟨Query.keccak (addr20 P.A ++ u256 0), ?_, ?_⟩
  · simpa only [List.append_nil] using source_query_mem P evs s
  · exact Nat.lt_of_not_ge hn

theorem W1_source_nondegenerate (h : W1) :
    ∃ A, 2^64 ≤ K (addr20 A ++ u256 0) := by
  obtain ⟨P, evs, s, tx, g, s', _, _, _, _, _, hno⟩ := h
  exact ⟨P.A, source_nondegenerate_of_noBadEvent P (evs ++ [.spend tx g]) s' hno⟩

end MSP.NonVacuity
