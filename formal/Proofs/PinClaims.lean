import Spec
import Groth16.TwistCardinality
import Mutations.MembershipCertificate
import Mutations.RangeCertificate
import Mutations.DuplicateCertificate
import Mutations.SinkCertificate

/-!
# Statements the axiom audit pins beyond `Spec`

`Proofs/AxiomAudit.lean` pins these results by name. Stating them here, in a
locked module whose imports are all locked, fixes their meaning: the
instances an inline statement would pick up from the audit's unlocked
imports cannot change what they say.
-/

namespace MSP.PinClaims

/-- The membership mutant admits an assignment violating R3: a nonzero-value
input whose Merkle path does not reach the statement's root. -/
def membershipClause : Prop :=
  ∃ a : Assignment, Mutations.Membership.system.Satisfied a ∧
    ∃ k, (witOf a).v k ≠ 0 ∧
      MR ((witOf a).leaf k) ((witOf a).idx k) ((witOf a).sib k) ≠ (stmtOf a).root

/-- The range mutant admits an assignment violating R5 on the first input value. -/
def rangeClause : Prop :=
  ∃ a : Assignment, Mutations.Range.system.Satisfied a ∧ ¬ ((witOf a).v 0).val < 2 ^ 128

/-- The duplicate mutant admits an assignment violating R8: equal nullifiers. -/
def duplicateClause : Prop :=
  ∃ a : Assignment, Mutations.Duplicate.system.Satisfied a ∧ (stmtOf a).nf1 = (stmtOf a).nf2

/-- The sink mutant admits an assignment violating R7: a zero-value first
output whose `inner` is not 1. -/
def sinkClause : Prop :=
  ∃ a : Assignment, Mutations.Sink.system.Satisfied a ∧ (witOf a).ov 0 = 0 ∧ (witOf a).oi 0 ≠ 1

/-- The order-`p` subgroup of the twist has exactly `p` points. -/
def g2Card : Prop := Nat.card (Groth16.Subgroup.primeTorsion Groth16.TwistPoint) = p

/-- `Groth16Accepts` unfolds to strict decoding, canonical nonzero coordinates
on the curves, the G2 subgroup check and the verification equation. -/
def groth16AcceptsIff : Prop :=
  ∀ (bytes : List UInt8) (pub : F × F × F),
    Groth16Accepts bytes pub ↔
      ∃ π : Groth16.ProofCoordinates,
        bytes.length = 256 ∧ Groth16.fromWords (Groth16.proofWords bytes) = π ∧
        π.Canonical ∧ π.Nonzero ∧ ∃ hc : π.OnCurve,
          ∃ hb : p • π.b.toTwistPoint hc.2.1 = 0,
            Groth16.VerificationEquation (π.a.toPoint hc.1)
              ⟨π.b.toTwistPoint hc.2.1, hb⟩ (π.c.toPoint hc.2.2) pub

end MSP.PinClaims
