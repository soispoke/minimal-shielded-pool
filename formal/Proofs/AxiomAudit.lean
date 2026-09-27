import Proofs.Model
import Proofs.Composition
import Proofs.CircuitArithmetic
import Proofs.CircuitGadgets
import Proofs.C6
import Artifacts.FullCompression
import Artifacts.Range
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Fail the build if a checked theorem starts depending on an admission or
an axiom beyond Lean's standard logical axioms. This audits the named proofs;
it does not discharge their hypotheses or bind the opaque artifact declarations. -/

open Lean Elab Command in
elab "assert_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed : List Name := [`propext, `choice, `Classical.choice, `Quot.sound]
  let extra := axioms.filter fun ax => !allowed.contains ax
  unless extra.isEmpty do
    throwError "{n} depends on nonstandard axioms: {extra}"

assert_standard_axioms model_theorem
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
