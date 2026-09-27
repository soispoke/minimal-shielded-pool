import Proofs.Effects
import Proofs.Composition
import Proofs.CircuitArithmetic
import Proofs.CircuitGadgets
import Proofs.C6
import Artifacts.FullCompression
import Artifacts.Range
import Artifacts.RangeAmounts
import Artifacts.RangeAddress
import Artifacts.BasicGates
import Artifacts.RelationFragments
import Artifacts.PathIndex
import Artifacts.PublicSignals
import Poseidon.Optimized3Equivalence
import Poseidon.Optimized4Equivalence
import Artifacts.PinnedRangeCompleteness
import Artifacts.InputCompleteness
import Artifacts.CircuitSoundness
import Artifacts.ControlCompleteness
import Artifacts.HashTraceCompleteness
import Artifacts.AssignmentRecoveryBeta
import Artifacts.PathCompletenessGates
import Artifacts.BaseAssignment
import Artifacts.GammaCompleteness
import Artifacts.RangeAssignmentCompleteness
import Artifacts.AssignmentRecoverySmall
import Artifacts.HashAssignmentCompletenessSmall
import Artifacts.ConstraintCoverage
import Artifacts.AssignmentAssembly
import Artifacts.CircuitCompleteness
import Proofs.CircuitModel
import Keccak.Labels
import Keccak.Vectors
import Groth16.KeyData
import Groth16.Encoding
import Proofs.NonVacuityEncoding
import Proofs.NonVacuityFixtureVerified
import Groth16.Group
import Groth16.SubgroupKey
import Groth16.Cardinality
import Proofs.Groth16Binding
import Chain.Dispatcher
import Mutations.Check
import Mutations.MembershipCounterexample
import Mutations.RangeCounterexample
import Mutations.DuplicateCounterexample
import Mutations.SinkCounterexample
import Proofs.PinClaims
import Proofs.AuditCommand

/-! Fail the build if a checked theorem starts depending on an admission or
an axiom beyond Lean's standard logical axioms. This audits the named proofs;
it does not discharge their hypotheses. -/

-- `assert_standard_axioms` is defined in `Proofs.AuditCommand`, which imports
-- only core Lean, so no module imported here can change what it checks.

assert_standard_axioms MSP.model_theorem
assert_standard_axioms MSP.c5j
assert_standard_axioms MSP.c5k
assert_standard_axioms MSP.c5l
assert_standard_axioms MSP.c5m
assert_standard_axioms MSP.c5n
assert_standard_axioms MSP.step_functional
assert_standard_axioms MSP.run_nodup
assert_standard_axioms MSP.spent_nodup_of_c5b
assert_standard_axioms MSP.composes
assert_standard_axioms MSP.nat_eq_of_field_eq
assert_standard_axioms MSP.value_conservation_iff
assert_standard_axioms MSP.input_sum_pos
assert_standard_axioms MSP.scalar_prime
assert_standard_axioms MSP.boolean_constraint
assert_standard_axioms MSP.isZero_sound
assert_standard_axioms MSP.isZero_complete
assert_standard_axioms MSP.bitsValue_cast
assert_standard_axioms MSP.bitsValue_lt
assert_standard_axioms MSP.num2Bits_range
assert_standard_axioms MSP.c6
assert_standard_axioms MSP.Artifacts.Compression.gamma_of_constraints
assert_standard_axioms MSP.Artifacts.Compression.gamma_of_system
assert_standard_axioms MSP.Artifacts.FullCompression.gamma_of_pinned_r1cs
assert_standard_axioms MSP.Artifacts.Range.first_input_range
assert_standard_axioms MSP.Artifacts.RangeAmounts.all_amount_ranges
assert_standard_axioms MSP.Artifacts.RangeAmounts.integer_conservation
assert_standard_axioms MSP.Artifacts.RangeAddress.address_ranges
assert_standard_axioms MSP.Artifacts.InputNonzero.positive_input_value
assert_standard_axioms MSP.Artifacts.BasicGates.statement_checks
assert_standard_axioms MSP.Artifacts.SinkGates.sink_rules
assert_standard_axioms MSP.Artifacts.ConcreteWitness.R1
assert_standard_axioms MSP.Artifacts.ConcreteWitness.index_cast
assert_standard_axioms MSP.Artifacts.ConcreteWitness.public_gamma
assert_standard_axioms MSP.Artifacts.RelationFragments.relation_of_hash_bindings
assert_standard_axioms MSP.Artifacts.PathIndex.MR_eq_raw_fold
assert_standard_axioms MSP.Artifacts.RelationFragments.relation_of_gadget_hashes
assert_standard_axioms MSP.Poseidon.Optimized.hash10_eq_reference
assert_standard_axioms MSP.Artifacts.PublicSignals.compression_of_pinned_r1cs
assert_standard_axioms MSP.Poseidon.Optimized3.hash2_eq_reference
assert_standard_axioms MSP.Poseidon.Optimized4.hash3_eq_reference
assert_standard_axioms MSP.CircuitCompleteness.num2Bits_complete
assert_standard_axioms MSP.Artifacts.RangeCompleteness.gate_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.first_input_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.second_input_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.first_output_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.second_output_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.public_amount_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.fee_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.recipient_complete
assert_standard_axioms MSP.Artifacts.PinnedRangeCompleteness.authorizer_complete
assert_standard_axioms MSP.Artifacts.InputCompleteness.input_gate_complete
assert_standard_axioms MSP.c1

assert_standard_axioms MSP.Artifacts.ControlCompleteness.complete_holds_of_relation
assert_standard_axioms MSP.Artifacts.HashTraceCompleteness.construct
assert_standard_axioms MSP.Artifacts.AssignmentRecoveryBeta.realizes

assert_standard_axioms MSP.Artifacts.PathCompleteness.complete_path
assert_standard_axioms MSP.Artifacts.BaseAssignment.projections_of_agreement
assert_standard_axioms MSP.Artifacts.GammaCompleteness.base_complete_holds
assert_standard_axioms MSP.Artifacts.RangeAssignmentCompleteness.complete_holds
assert_standard_axioms MSP.Artifacts.AssignmentRecoverySmall.realizes
assert_standard_axioms MSP.Artifacts.HashAssignmentCompletenessSmall.complete
assert_standard_axioms MSP.Artifacts.ConstraintCoverage.satisfied_of_fragments
assert_standard_axioms MSP.Artifacts.AssignmentAssembly.satisfied

assert_standard_axioms MSP.c1c

assert_standard_axioms MSP.circuit_model
assert_standard_axioms MSP.main_theorem_of_chain
assert_standard_axioms MSP.chain_corollary_of_chain

assert_standard_axioms MSP.K_lt
assert_standard_axioms MSP.Keccak.hash_lt
assert_standard_axioms MSP.Keccak.domain_one_one_zero_eq
assert_standard_axioms MSP.Keccak.source_one_zero_nondegenerate
assert_standard_axioms MSP.Groth16.pinnedKey_coordinateChecks
assert_standard_axioms MSP.Groth16.G2Coordinates.onCurve_iff
assert_standard_axioms MSP.Groth16.decodeProof_eq_some_iff
assert_standard_axioms MSP.Groth16.decoded_g2_order
assert_standard_axioms MSP.NonVacuity.decode_encodeSettlement
assert_standard_axioms MSP.NonVacuity.encodeTx_Acc

assert_standard_axioms MSP.w1

assert_standard_axioms BN254.BaseField_is_prime
assert_standard_axioms MSP.Groth16.g1Curve_discriminant_ne_zero
assert_standard_axioms MSP.Groth16.G1Coordinates.toPoint_coordinates
assert_standard_axioms MSP.Groth16.G1Coordinates.toPoint_injective
assert_standard_axioms MSP.Groth16.G1Point.coordinates_toPoint
assert_standard_axioms MSP.Groth16.fq_neg_one_not_square
assert_standard_axioms MSP.Groth16.fq2ToField_twistB
assert_standard_axioms MSP.Groth16.twistCurve_discriminant_ne_zero
assert_standard_axioms MSP.Groth16.G2Coordinates.toTwistPoint_injective
assert_standard_axioms MSP.Groth16.TwistPoint.coordinates_toTwistPoint
assert_standard_axioms MSP.Groth16.Subgroup.pinnedKey_subgroupChecks
assert_standard_axioms MSP.Groth16.Subgroup.pinnedKey_pointOrders
assert_standard_axioms MSP.Groth16.Subgroup.g1BasePoint_order
assert_standard_axioms MSP.Groth16.g1Point_card
assert_standard_axioms MSP.Groth16.g1BasePoint_generates
assert_standard_axioms MSP.Groth16.g1Point_exists_unique_scalar
assert_standard_axioms MSP.Groth16.g1Point_scalar_prime_torsion
assert_standard_axioms MSP.Groth16.G1Coordinates.toPoint_order
assert_standard_axioms MSP.Chain.Dispatcher.sender_mismatch_pinned
assert_standard_axioms MSP.Mutations.satisfied_of_blocks

/-! Pin the statement of every principal result to the locked `Spec` claim, so
weakening a theorem, for example by adding a hypothesis, fails the build. Each
pin is a theorem whose own axioms are audited, so a coercion that elaboration
inserts to make a weaker proof fit the claim must itself be proved. -/
theorem pin_c1 : MSP.C1 := MSP.c1
theorem pin_c1c : MSP.C1c := MSP.c1c
theorem pin_model_theorem : MSP.ModelTheorem := MSP.model_theorem
theorem pin_c6 : MSP.C6 := MSP.c6
theorem pin_w1 : MSP.W1 := MSP.w1
theorem pin_composes : MSP.Composes := MSP.composes
theorem pin_circuit_model : MSP.C1 ∧ MSP.C1c ∧ MSP.ModelTheorem := MSP.circuit_model
theorem pin_main_theorem_of_chain :
    MSP.C2 → MSP.C2c → MSP.C8 → MSP.C9 → MSP.C10 → MSP.Refines → MSP.MainTheorem :=
  MSP.main_theorem_of_chain
theorem pin_chain_corollary_of_chain :
    MSP.C2 → MSP.C2c → MSP.C8 → MSP.C9 → MSP.C10 → MSP.Refines → MSP.ChainCorollary :=
  MSP.chain_corollary_of_chain

assert_standard_axioms pin_c1
assert_standard_axioms pin_c1c
assert_standard_axioms pin_model_theorem
assert_standard_axioms pin_c6
assert_standard_axioms pin_w1
assert_standard_axioms pin_composes
assert_standard_axioms pin_circuit_model
assert_standard_axioms pin_main_theorem_of_chain
assert_standard_axioms pin_chain_corollary_of_chain

theorem pin_original_c1_iff :
    MSP.Mutations.C1For MSP.Artifacts.Spend.system ↔ MSP.C1 :=
  MSP.Mutations.original_c1_iff

assert_standard_axioms pin_original_c1_iff

theorem pin_membership_c1_fails : ¬ MSP.Mutations.C1For MSP.Mutations.Membership.system :=
  MSP.Mutations.Membership.c1_fails

assert_standard_axioms pin_membership_c1_fails

theorem pin_membership_counterexample : ∃ a : MSP.Assignment,
    MSP.Mutations.Membership.system.Satisfied a ∧ ¬ MSP.R (MSP.stmtOf a) (MSP.witOf a) :=
  MSP.Mutations.Membership.counterexample

assert_standard_axioms pin_membership_counterexample

theorem pin_membership_clause : MSP.PinClaims.membershipClause :=
  MSP.Mutations.Membership.clause_fails

assert_standard_axioms pin_membership_clause

theorem pin_range_c1_fails : ¬ MSP.Mutations.C1For MSP.Mutations.Range.system :=
  MSP.Mutations.Range.c1_fails

assert_standard_axioms pin_range_c1_fails

theorem pin_range_counterexample : ∃ a : MSP.Assignment,
    MSP.Mutations.Range.system.Satisfied a ∧ ¬ MSP.R (MSP.stmtOf a) (MSP.witOf a) :=
  MSP.Mutations.Range.counterexample

assert_standard_axioms pin_range_counterexample

theorem pin_range_clause : MSP.PinClaims.rangeClause :=
  MSP.Mutations.Range.clause_fails

assert_standard_axioms pin_range_clause

theorem pin_duplicate_c1_fails : ¬ MSP.Mutations.C1For MSP.Mutations.Duplicate.system :=
  MSP.Mutations.Duplicate.c1_fails

assert_standard_axioms pin_duplicate_c1_fails

theorem pin_duplicate_counterexample : ∃ a : MSP.Assignment,
    MSP.Mutations.Duplicate.system.Satisfied a ∧ ¬ MSP.R (MSP.stmtOf a) (MSP.witOf a) :=
  MSP.Mutations.Duplicate.counterexample

assert_standard_axioms pin_duplicate_counterexample

theorem pin_duplicate_clause : MSP.PinClaims.duplicateClause :=
  MSP.Mutations.Duplicate.clause_fails

assert_standard_axioms pin_duplicate_clause

theorem pin_sink_c1_fails : ¬ MSP.Mutations.C1For MSP.Mutations.Sink.system :=
  MSP.Mutations.Sink.c1_fails

assert_standard_axioms pin_sink_c1_fails

theorem pin_sink_counterexample : ∃ a : MSP.Assignment,
    MSP.Mutations.Sink.system.Satisfied a ∧ ¬ MSP.R (MSP.stmtOf a) (MSP.witOf a) :=
  MSP.Mutations.Sink.counterexample

assert_standard_axioms pin_sink_counterexample

theorem pin_sink_clause : MSP.PinClaims.sinkClause :=
  MSP.Mutations.Sink.clause_fails

assert_standard_axioms pin_sink_clause

-- Concrete G2 and textbook verifier bindings, separate from bytecode C9.
assert_standard_axioms MSP.Groth16.cofactorPoint_order
assert_standard_axioms MSP.Groth16.twistPoint_card_not_scalar_square
assert_standard_axioms MSP.Groth16.g2Point_natCard
assert_standard_axioms MSP.Groth16.g2BasePoint_generates
assert_standard_axioms MSP.Groth16.g2Point_exists_unique_scalar
assert_standard_axioms MSP.Groth16.twistPoint_mem_g2_iff
assert_standard_axioms MSP.Groth16.g1Log_spec
assert_standard_axioms MSP.Groth16.g2Log_spec
assert_standard_axioms MSP.Groth16.pairingExponent_nonzero_left
assert_standard_axioms MSP.Groth16.pairingExponent_nonzero_right
assert_standard_axioms MSP.Groth16.verificationEquation_iff
assert_standard_axioms MSP.groth16_accepts_iff
assert_standard_axioms MSP.groth16_accepts_point_orders

private theorem pin_g2_card : MSP.PinClaims.g2Card := MSP.Groth16.g2Point_natCard
assert_standard_axioms pin_g2_card

private theorem pin_groth16_accepts : MSP.PinClaims.groth16AcceptsIff :=
  MSP.groth16_accepts_iff
assert_standard_axioms pin_groth16_accepts
