import Artifacts.Witness
import Artifacts.RangeAmounts
import Artifacts.RangeAddress
import Artifacts.BasicGates
import Artifacts.SinkGates
import Artifacts.PathGates

/-! Assemble every non-hash conjunct of the canonical spend relation from the
complete pinned R1CS. The hash equations and gated Merkle membership are explicit
remaining premises. `CircuitSoundness` discharges those premises to
prove C1. -/

namespace MSP.Artifacts.RelationFragments

open ConcreteWitness

/-- R5 through R9, including the amount list, for the concrete projections. -/
theorem non_hash_checks (a : Assignment) (h : Spend.system.Satisfied a) :
    let x := statementOf a
    let w := ofAssignment a
    (∀ y ∈ [w.v 0, w.v 1, w.ov 0, w.ov 1, x.pub, x.fee], y.val < 2^128) ∧
    (w.v 0).val + (w.v 1).val =
      (w.ov 0).val + (w.ov 1).val + x.pub.val + x.fee.val ∧
    0 < (w.v 0).val + (w.v 1).val ∧
    (∀ k : Fin 2, (w.ov k = 0 → w.oi k = ((k.val + 1 : ℕ) : F)) ∧
      (w.ov k ≠ 0 → w.oi k ≠ 1 ∧ w.oi k ≠ 2)) ∧
    x.nf1 ≠ x.nf2 ∧ x.o1 ≠ x.o2 ∧
    x.rcp.val < 2^160 ∧ 0 < x.auth.val ∧ x.auth.val < 2^160 ∧
    (x.pub = 0 ↔ x.rcp = 0) := by
  have hb := RangeAmounts.all_amount_ranges a h
  refine ⟨?_, RangeAmounts.integer_conservation a h,
    InputNonzero.positive_input_value a h, ?_,
    BasicGates.nullifiers_distinct a h, BasicGates.outputs_distinct a h,
    RangeAddress.recipient_range a h, BasicGates.authorizer_positive a h,
    RangeAddress.authorizer_range a h, BasicGates.public_zero_iff_recipient_zero a h⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2.1
    · exact hb.2.2.2.2.1
    · exact hb.2.2.2.2.2
  · intro k
    fin_cases k
    · exact SinkGates.first_output_sink_rules a h
    · exact SinkGates.second_output_sink_rules a h

/-- All remaining relation obligations are exposed as hash/path premises.
Discharging them from the actual gates is still required for circuit soundness. -/
theorem relation_of_hash_bindings (a : Assignment) (h : Spend.system.Satisfied a)
    (hnf1 : (statementOf a).nf1 = nf (statementOf a).d
      ((ofAssignment a).sk 0) ((ofAssignment a).leaf 0) ((ofAssignment a).idx 0))
    (hnf2 : (statementOf a).nf2 = nf (statementOf a).d
      ((ofAssignment a).sk 1) ((ofAssignment a).leaf 1) ((ofAssignment a).idx 1))
    (hpath : ∀ k, (ofAssignment a).v k ≠ 0 →
      MR ((ofAssignment a).leaf k) ((ofAssignment a).idx k)
        ((ofAssignment a).sib k) = (statementOf a).root)
    (hout1 : (statementOf a).o1 = cm ((ofAssignment a).oi 0) ((ofAssignment a).ov 0))
    (hout2 : (statementOf a).o2 = cm ((ofAssignment a).oi 1) ((ofAssignment a).ov 1)) :
    R (statementOf a) (ofAssignment a) :=
  ⟨ConcreteWitness.R1 a h, hnf1, hnf2, hpath, hout1, hout2, non_hash_checks a h⟩

/-- Use the checked selector and root gates to reduce the remaining Merkle
premise to leaf and individual node hash equations on actual wires. -/
theorem relation_of_gadget_hashes (a : Assignment) (h : Spend.system.Satisfied a)
    (hnf1 : (statementOf a).nf1 = nf (statementOf a).d
      ((ofAssignment a).sk 0) ((ofAssignment a).leaf 0) ((ofAssignment a).idx 0))
    (hnf2 : (statementOf a).nf2 = nf (statementOf a).d
      ((ofAssignment a).sk 1) ((ofAssignment a).leaf 1) ((ofAssignment a).idx 1))
    (hleaf : ∀ k, a (PathGatesData.curStart k) = (ofAssignment a).leaf k)
    (hnodes : ∀ k, PathGates.NodeHashes a k)
    (hout1 : (statementOf a).o1 = cm ((ofAssignment a).oi 0) ((ofAssignment a).ov 0))
    (hout2 : (statementOf a).o2 = cm ((ofAssignment a).oi 1) ((ofAssignment a).ov 1)) :
    R (statementOf a) (ofAssignment a) :=
  relation_of_hash_bindings a h hnf1 hnf2
    (fun k hv => PathGates.membership_of_hashes a h k (hleaf k) (hnodes k) hv) hout1 hout2

#print axioms non_hash_checks
#print axioms relation_of_hash_bindings
#print axioms relation_of_gadget_hashes

end MSP.Artifacts.RelationFragments
