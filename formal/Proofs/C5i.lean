import Proofs.Path

/-! C5i from C5b. -/

namespace MSP
noncomputable section
open Classical

theorem bad_with_of_bad (P : Pool) (evs : List Event) (s : PoolState) (ex : List Query) :
    BadEvent P evs s → BadEventWith P evs s ex := by
  have hsub : ∀ q ∈ traceQueries P evs s ++ [], q ∈ traceQueries P evs s ++ ex := by
    intro q hq; simp at hq; exact List.mem_append_left _ hq
  rintro (⟨q1, h1, q2, h2, hc⟩ | ⟨q, hq, hd⟩ | hc | hc)
  · exact Or.inl ⟨q1, hsub _ h1, q2, hsub _ h2, hc⟩
  · exact Or.inr (Or.inl ⟨q, hsub _ hq, hd⟩)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hc))

theorem mem_witnessQueries_k (x : Statement) (w : Witness) (k : Fin 2) :
    Query.h3 1 (w.sk k) 0 ∈ witnessQueries x w ∧
    Query.h2 (pk (w.sk k)) (w.ρ k) ∈ witnessQueries x w ∧
    Query.h3 2 (inner (w.sk k) (w.ρ k)) (w.v k) ∈ witnessQueries x w ∧
    ∀ q ∈ pathQueries (w.leaf k) (w.idx k) (w.sib k), q ∈ witnessQueries x w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · intros
    unfold witnessQueries
    apply List.mem_append_left
    rw [List.mem_flatMap]
    exact ⟨k, List.mem_finRange k, by simp_all⟩

theorem spend_wq_in_trace (P : Pool) (evs : List Event) (tx : FrameTx) (g : ℕ) (s : PoolState) :
    ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) (witOf (extOf P tx)),
      q ∈ traceQueries P (evs ++ [.spend tx g]) s := by
  intro q hq
  unfold traceQueries
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  exact ⟨.spend tx g, by simp, by
    simp only [eventQueries]; exact List.mem_append_left _ (List.mem_append_left _ hq)⟩

theorem c5i_of (P : Pool) (h5b : C5b P) : C5i P := by
  intro evs s tx g s' hrun hs o sk ρ v k hi hleaf hvk ho
  rcases h5b evs s tx g s' hrun hs with hb | ⟨hin, -⟩
  · left; exact bad_with_of_bad P _ _ _ hb
  obtain ⟨-, hL, -, -⟩ := hin k hvk
  subst ho
  set w := witOf (extOf P tx)
  have heq : cm (inner (w.sk k) (w.ρ k)) (w.v k) = cm (inner sk ρ) v := by
    rw [← hleaf]; exact hL.symm
  set T := traceQueries P (evs ++ [.spend tx g]) s' ++
    openingQueries P (settleData tx).epoch (w.idx k) sk ρ v
  by_cases hNC : NoColl T
  swap
  · left; left
    unfold NoColl at hNC; push Not at hNC
    obtain ⟨q1, h1, q2, h2, hc⟩ := hNC
    exact ⟨q1, h1, q2, h2, hc⟩
  right
  obtain ⟨w1, w2, w3, -⟩ := mem_witnessQueries_k (stmtOf (extOf P tx)) w k
  have inT : ∀ q ∈ witnessQueries (stmtOf (extOf P tx)) w, q ∈ T := fun q hq =>
    List.mem_append_left _ (spend_wq_in_trace P evs tx g s' q hq)
  have o1 : Query.h3 1 sk 0 ∈ T := List.mem_append_right _ (by simp [openingQueries])
  have o2 : Query.h2 (pk sk) ρ ∈ T := List.mem_append_right _ (by simp [openingQueries])
  have o3 : Query.h3 2 (inner sk ρ) v ∈ T := List.mem_append_right _ (by simp [openingQueries])
  obtain ⟨-, hin, -⟩ := h3_inj hNC (inT _ w3) o3 heq
  obtain ⟨hpk, hρ⟩ := h2_inj hNC (inT _ w2) o2 hin
  obtain ⟨-, hsk, -⟩ := h3_inj hNC (inT _ w1) o1 hpk
  exact ⟨hsk, hρ⟩

#print axioms c5i_of

end
end MSP
