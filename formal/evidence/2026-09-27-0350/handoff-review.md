# Checked increments prepared for Claude handoff

The user asked Claude at 05:48 UTC on September 27 to continue from Codex.
Claude created `prototypes/msp-formal-claude`, branch
`claude/formal-spec-continued`, from `411f952`. Its six specification reviewers
are active. Codex is preserving in-flight work and ending its ownership.
The automation was found already PAUSED; that status is preserved.

## Group certificates

Reviewed the actual Fq² construction, twist equation and nonsingularity,
coordinate injections and round trips, and generic tangent/secant/opposite
certificates. The numerical traces are checked against Mathlib's group law.
`pinnedKey_subgroupChecks`, `pinnedKey_pointOrders` and `g1BasePoint_order`
certify the eight key points and base point, without assuming their orders.
All nine generated traces reproduce exactly. The one-unit slope negative
control fails in Lean as intended. The axiom reports contain only standard
logical axioms. This does not define the pairing or discharge chain C2.

## Dispatcher pilot

Reviewed the partial opcode interpreter, real runtime extraction and symbolic
24-step sender-mismatch trace. The decoder rejects unsupported in-code bytes;
missing bytes mean STOP. The total jump scan skips PUSH payloads and advances
over other bytes. SUB/SHL stack order, pure memory, expansion costs, gas
subtraction and REVERT output agree with this bounded path. The checked result
uses exact pinned bytes and arbitrary immutable tail, preserves carried state
and costs 80 execution gas using pinned ethrex TXPARAM cost 2.

The source/generator boundary is explicit. Runtime extraction proves a literal
slice and constructor operands, not full creation execution. The interpreter
has no effectful opcodes, frame-entry validation, intrinsic gas or complete
state-gas rules. It is not wired into the opaque canonical chain semantics.
The real on-chain refinement and successful paths remain open.

## Mutation evidence

Reviewed the four changed source sites, strict witness decoding, full modular
constraint evaluation, original-generator rejection, and exact canonical
relation-clause evaluation. The baseline reproduces both original R1CS and
symbol hashes. Archive and raw artifact hashes bind the saved witnesses and
compiled mutants. Six validator tests passed. snarkjs and Python use separate
arithmetic, but share the r1csfile decoder; this boundary is documented.

The four counterexamples are executable evidence. The generic Lean checker
reflection theorem builds; its proposed concrete membership fixture is parked
with a recursion-depth elaboration failure and no claimed certified mutant.
No canonical proposition was weakened and no mutation gate is marked closed.

## Final integration check

`lake build` passes all 3,661 jobs after integrating the checked increments.
`Proofs.AxiomAudit` now covers the subgroup, dispatcher and generic constraint
reflection results. No pending source is imported into the successful build.
The full output is `handoff-full-build.log`. Existing `c1-artifact-tests.log`
is an earlier successful 61-test run, not a new check at handoff.
