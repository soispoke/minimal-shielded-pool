import Proofs.NonVacuityFixture

/-! A finite certificate interface for W1's exact compact query support.
Every listed value must be proved equal to the concrete hash. Injectivity is
checked only for this finite table; no global hash assumption occurs here. -/

namespace MSP.NonVacuity

deriving instance DecidableEq for Query

def queryValue : Query → ℕ
  | .h2 a b => (H2 a b).val
  | .h3 a b c => (H3 a b c).val
  | .keccak m => K m
  | .dom c a e => (D c a e).val

theorem collide_ne (q₁ q₂ : Query) (h : q₁.collide q₂) : q₁ ≠ q₂ := by
  intro he
  subst q₂
  cases q₁ <;> simp [Query.collide] at h

theorem collide_value (q₁ q₂ : Query) (h : q₁.collide q₂) :
    queryValue q₁ = queryValue q₂ := by
  cases q₁ <;> cases q₂ <;> simp only [Query.collide] at h <;>
    try contradiction
  all_goals simp only [queryValue, h.2]

theorem not_degenerate_of_value (q : Query) (n : ℕ) (hv : queryValue q = n)
    (hlarge : 2 ^ 64 ≤ n) : ¬ q.degenerate := by
  cases q with
  | h2 a b =>
    intro hd
    change H2 a b = 0 at hd
    simp only [queryValue, hd, ZMod.val_zero] at hv
    omega
  | h3 a b c =>
    intro hd
    change H3 a b c = 0 at hd
    simp only [queryValue, hd, ZMod.val_zero] at hv
    omega
  | keccak m =>
    change ¬ K m < 2 ^ 64
    change K m = n at hv
    omega
  | dom c a e => exact not_false

/-- Numeric table checks allow repeated identical queries. A repeated output
is permitted exactly when its query is also identical. -/
def TableUnique (table : List (Query × ℕ)) : Prop :=
  ∀ q₁ n₁, (q₁, n₁) ∈ table → ∀ q₂ n₂, (q₂, n₂) ∈ table →
    n₁ = n₂ → q₁ = q₂

/-- The finite executable pairwise check implies the quantified table
property. The diagonal needs no assumption and duplicate queries are safe. -/
theorem tableUnique_of_pairwise (table : List (Query × ℕ))
    (h : table.Pairwise (fun a b => a.2 = b.2 → a.1 = b.1)) : TableUnique table := by
  induction table with
  | nil => simp [TableUnique]
  | cons a tail ih =>
    rcases List.pairwise_cons.mp h with ⟨hh, ht⟩
    intro q₁ n₁ hm₁ q₂ n₂ hm₂ he
    rcases List.mem_cons.mp hm₁ with h₁ | h₁
    · subst a
      rcases List.mem_cons.mp hm₂ with h₂ | h₂
      · exact (Prod.mk.inj h₂).1.symm
      · exact hh _ h₂ he
    · rcases List.mem_cons.mp hm₂ with h₂ | h₂
      · subst a
        exact (hh _ h₁ he.symm).symm
      · exact ih ht q₁ n₁ h₁ q₂ n₂ h₂ he

theorem no_collisions_of_table (queries : List Query) (table : List (Query × ℕ))
    (hs : ∀ q ∈ queries, ∃ n, (q, n) ∈ table)
    (hv : ∀ q n, (q, n) ∈ table → queryValue q = n)
    (hu : TableUnique table) :
    ¬ ∃ q₁ ∈ queries, ∃ q₂ ∈ queries, q₁.collide q₂ := by
  rintro ⟨q₁, hq₁, q₂, hq₂, hc⟩
  obtain ⟨n₁, hn₁⟩ := hs q₁ hq₁
  obtain ⟨n₂, hn₂⟩ := hs q₂ hq₂
  have he := collide_value q₁ q₂ hc
  rw [hv q₁ n₁ hn₁, hv q₂ n₂ hn₂] at he
  exact collide_ne q₁ q₂ hc (hu q₁ n₁ hn₁ q₂ n₂ hn₂ he)

theorem no_degeneracy_of_table (queries : List Query) (table : List (Query × ℕ))
    (hs : ∀ q ∈ queries, ∃ n, (q, n) ∈ table)
    (hv : ∀ q n, (q, n) ∈ table → queryValue q = n)
    (hl : ∀ q n, (q, n) ∈ table → 2 ^ 64 ≤ n) :
    ¬ ∃ q ∈ queries, q.degenerate := by
  rintro ⟨q, hq, hd⟩
  obtain ⟨n, hn⟩ := hs q hq
  exact not_degenerate_of_value q n (hv q n hn) (hl q n hn) hd

theorem no_badEvent_of_table (P : Pool) (events : List Event) (s : PoolState)
    (table : List (Query × ℕ))
    (hs : ∀ q ∈ compactTraceQueries P events s, ∃ n, (q, n) ∈ table)
    (hv : ∀ q n, (q, n) ∈ table → queryValue q = n)
    (hu : TableUnique table)
    (hl : ∀ q n, (q, n) ∈ table → 2 ^ 64 ≤ n)
    (hc : ¬ CompressionBreak P events) (he : ¬ ExtractionFailure P events) :
    ¬ BadEvent P events s := by
  rw [badEvent_iff_compact]
  exact fun h => h.elim (no_collisions_of_table _ table hs hv hu)
    (fun h => h.elim (no_degeneracy_of_table _ table hs hv hl)
      (fun h => h.elim hc he))

theorem fixture_only_spend (tx tx' : FrameTx) (g g' : ℕ)
    (h : Event.spend tx' g' ∈ fixtureEvents ++ [.spend tx g]) : tx' = tx ∧ g' = g := by
  simpa [fixtureEvents] using h

theorem fixture_no_extraction_failure (A c : ℕ) (a : Assignment) (ha : Satisfied a)
    (tx : FrameTx) (g : ℕ) (hp : verifiedPublics tx = publicOf a) :
    ¬ ExtractionFailure (idealPool A c a) (fixtureEvents ++ [.spend tx g]) := by
  rintro ⟨tx', g', hm, hf⟩
  obtain ⟨rfl, rfl⟩ := fixture_only_spend tx tx' g g' hm
  apply hf
  simp only [extOf, hp, idealPool_preferred]
  exact ⟨ha, trivial⟩

theorem fixture_no_compression_break (A c : ℕ) (a : Assignment)
    (tx : FrameTx) (g : ℕ) (hp : verifiedPublics tx = publicOf a)
    (hx : stmtOf a = (settleData tx).stmt) :
    ¬ CompressionBreak (idealPool A c a) (fixtureEvents ++ [.spend tx g]) := by
  rintro ⟨tx', g', hm, _, _, hne⟩
  obtain ⟨rfl, rfl⟩ := fixture_only_spend tx tx' g g' hm
  apply hne
  simpa only [extOf, hp, idealPool_preferred] using hx

end MSP.NonVacuity
