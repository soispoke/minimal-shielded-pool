# Focused C1/C1c review

Reviewer: Codex subagent `/root/composition_proof`, inherited model (specific model identifier not exposed). Read-only review after the checked C1c build; the reviewer previously authored the concrete layout certificates.

Reviewed canonical C1/C1c, concrete circuit wrappers, soundness, constructive hash witnesses, semantic seed, generic assignment assembly, exact projections and constraint coverage. No substantive scope or correctness defect found. The proof preserves arbitrary alpha, the entire private witness, statement and public triple. The seed derives hash values from R and definitions, not circuit satisfaction. Checked write ownership, boundary agreement, read support and reverse coverage close every actual constraint.

C1c source SHA-256: `3a55fddef53554128814805daa2920f014d02906ecb7735ea3a842ae68a63066`. `lake build Artifacts.CircuitCompleteness` passed 3,517 jobs; the full default build passed 3,563 jobs. The principal axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Remaining boundary: binary decoding and compiler/source/symbol provenance are external audited regeneration and independent-decoder checks. C1/C1c do not discharge concrete verifier/chain semantics, W1/W2 or required semantic mutations. P3 and P9 remain canonical cryptographic premises.
