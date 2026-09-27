import Artifacts.BetaGatesCertificates
import Artifacts.Spend

/-! All 153 actual beta S-box triples, interpreted over every full satisfying assignment. -/

namespace MSP.Artifacts.BetaGates

open BetaGatesData

set_option maxRecDepth 65536

theorem constraints_eq_slice :
    constraints = ((Spend.group0 ++ Spend.group1).drop 9).take 459 := rfl

theorem constraint_mem {c : Constraint} (hc : c ∈ constraints) :
    c ∈ Spend.system.constraints := by
  rw [constraints_eq_slice] at hc
  have hm := List.mem_of_mem_drop (List.mem_of_mem_take hc)
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_flatten.mpr ⟨Spend.group0, by simp, hm⟩
  · exact List.mem_flatten.mpr ⟨Spend.group1, by simp, hm⟩

theorem triple_mem (t : Fin 153) (j : Fin 3) : triple t j ∈ Spend.system.constraints :=
  constraint_mem (List.getElem_mem _)

/-- A beta S-box's actual extracted output linear combination is its input to the fifth power. -/
theorem sigma_triple (w : Assignment) (h : Spend.system.Satisfied w) (t : Fin 153) :
    eval (output t) w = (eval (input t) w)^5 := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := BetaGatesCertificates.triple_signs t
  have e0 := eval_certificate _ _ s0 w
  have e1 := eval_certificate _ _ s1 w
  have e2 := eval_certificate _ _ s2 w
  have e3 := eval_certificate _ _ s3 w
  have e4 := eval_certificate _ _ s4 w
  simp only [eval_ofLC, eval_scale, neg_one_mul] at e0 e1 e2 e3 e4
  have h0 := h.2 _ (triple_mem t 0)
  have h1 := h.2 _ (triple_mem t 1)
  have h2 := h.2 _ (triple_mem t 2)
  unfold Constraint.Holds at h0 h1 h2
  rw [e0, e1] at h0
  rw [e2] at h1
  rw [e3, e4] at h2
  simp only [output, eval_scale, eval_ofLC, neg_one_mul]
  apply sigma_equations (eval (input t) w) ((triple t 1).b.eval w)
    (-((triple t 1).c.eval w)) (-((triple t 2).c.eval w))
  · simpa only [input, eval_ofLC] using h0
  · simpa only [neg_neg] using h1
  · simpa only [neg_neg] using h2

#print axioms sigma_triple

end MSP.Artifacts.BetaGates
