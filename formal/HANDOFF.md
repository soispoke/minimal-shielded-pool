# MSP formal verification continuation

## Active checkout

Codex took over on 2026-09-27 after Claude session
`e9529fa7-10f6-4fd3-a0b1-195641fd261d` stopped at 2026-09-26 22:36 UTC
with a session-limit error. Its round-12 reviewers also stopped.

The durable proof continuation is `/Volumes/PrivateAI/WorkRepos/HardnessVault/prototypes/msp-formal-verification`,
branch `codex/formal-continuation`. The checked composition, concrete C6,
full-R1CS compression and proof infrastructure are committed at
`c6bed8848374f85a00b8fececb5aaf4f70875477`. The subsequent first-input range
binding and final checks are at `ccf84b31361ea075f93879a99909ae5f1a1a3c20`.
The preserved base is `cb7c5a2` from
`claude/formal-spec`. This checkout has an independent Git object store; it
does not depend on the temporary Claude repository for source recovery.

The scheduled Codex task is `01a0dfaf-821e-7a11-b764-8ceeeb320135`, automation
`continue-msp-formal-verification`. Check that task and the original Claude
session for active work before editing. A quota reset does not itself transfer
ownership back to Claude. Coordinate an explicit handoff before two agents
write the same files.

**Concurrent work detected at 00:20 UTC on September 27:** Claude resumed at
00:11 UTC after the user requested continuation. Its original checkout is at
`e676226ed47e62aeacc694928d939a5247b362f4`, with the same round-12 event-decoding
fix described below. Round-13 specification reviewers are active, and the user
also started a separate "Gate zkey and verifier against spend.r1cs" task.
Do not interrupt them or launch duplicate review/artifact-gating workers.
Codex finished its already-owned range binding in this separate checkout and
released file ownership after checking and committing it. Before the next
proof edit, inspect fresh statuses and any new
specification findings. Reconcile the two branches once ownership is clear;
do not overwrite either branch or assume the original checkout is still idle.

## Scope and checks

`SPEC.md` is the canonical functional-verification scope. Read
`Proofs/README.md` for proven claims; `Spec/Main.lean` states the completion
theorems. Abstract model proofs do not discharge concrete circuit or chain
semantics bindings. C1/C1c, the chain half, W1/W2 and the mutation gates remain
open unless their proofs are recorded explicitly. C6 is now discharged for
the specified algorithm, but not for the deployed bytecode.

Run `/opt/homebrew/bin/lake build` from `formal/`. The takeover baseline passed
all 1,294 jobs. The main model theorem's axiom report contains only
`propext`, `Classical.choice` and `Quot.sound`. Existing style/deprecation
warnings are not proof failures.

The ignored `formal/.lake/packages` currently links to the original Claude
Mathlib cache. If that cache disappears, remove only the broken symlink and
restore the dependencies from `lake-manifest.json` using the pinned toolchain.
The source, manifest and proofs are preserved here. The ignored `build/spend.r1cs`
was copied from the original artifact for the step-3 checks. It can also be
reproduced from the pinned circuit and tooling lockfile. The stable tooling
cache at `/Volumes/PrivateAI/WorkRepos/minimal-shielded-pool/tooling/node_modules`
was used only for its matching dependencies, never for that checkout's sources.
The ignored `build/spend_final.zkey` is also copied here after checking its full
activation-manifest hash (`587c048b06d68c61dcb0a9a57b51229def97b219b11827042f4a8faa49499376`).
It was not regenerated. This preserves the pinned test setup while the separate
artifact-gating worker checks it. The original repository's `e676226` commit is
preserved locally as `refs/remotes/claude-checkpoint/formal-spec` for reconciliation.

## Work in this continuation

The unfinished round-12 event-decoding finding is fixed in `SPEC.md`,
`Spec/Evm.lean` and `Spec/System.lean`: function events must decode original
message calls entering the pool, before delegation, excluding VERIFY
execution. This prevents a dispatcher mutation from changing an input while
the model follows the changed input. The new mutation remains an obligation
for the concrete semantics, not a claimed executed test.

`Proofs/Composition.lean` proves `MSP.composes : Composes` from the unchanged
main theorem statement, with only standard Lean axioms. This closes the
conditional composition lemma, not its circuit or chain premises.

The concrete reference Poseidon definitions are now bound in `Spec/Hash.lean`.
`Proofs/PoseidonConstants.lean` checks all 21 zero-tree constants with ordinary
Lean `decide`. `Proofs/C6.lean` proves C6, using the previously established
algorithm lemma. Integrating C6 with the model exposed duplicate helper names
in `Sanity/C6Proof.lean`; reusing the identical `TreeLemma` declarations and
making the C6-local invariant private fixes the aggregate import failure.

`Artifacts/Spend.lean` contains all 14,802 constraints of the exact pinned R1CS.
`Artifacts/FullCompression.lean` proves the gamma polynomial from full-system
satisfaction, including kernel-checked containment of its nine constraints.
It does not assume containment or the desired polynomial. Beta, the other
gadgets, reconstructed eliminated signals and the full relation are still open.
`Spec/Circuit.lean` remains opaque pending those complete bindings.

`Proofs/CircuitArithmetic.lean` proves integer conservation from field
conservation and the six value bounds. `Proofs/CircuitGadgets.lean` proves
Boolean, IsZero and Num2Bits helper lemmas using a kernel-checked BN254
primality certificate from pinned, attributed Apache-licensed upstream code.
These helpers do not by themselves bind the production gadgets.

The subsequent `Artifacts/Range.lean` proof closes the first input's actual
range gate: `Range.first_input_range` derives `(w 10).val < 2^128` solely from
`Spend.system.Satisfied w`. It proves all 127 retained bits Boolean, reconstructs
the eliminated top bit from the actual last constraint, checks the coefficient
identity in Lean's kernel, and proves full-system containment. The other five
amount range gates remain open. `RangeLemmas.lean` supplies the reusable bridge.

The artifact parser records a reproducible compiler format defect: the exact
R1CS header says five sections although it contains three complete sections.
Strict parsing rejects it; the compatibility path requires the full pinned
SHA-256 and exact section order, then applies all other structural checks.
An independent lockfile-pinned decoder agrees on every constraint and label.
See `Artifacts/README.md` for the exception and remaining external parser trust.

## Reproduce

From `formal/`, `lake build` checks all six default libraries, including
`Proofs/AxiomAudit.lean`. The aggregate audit permits only `propext`, Lean's
choice axiom and `Quot.sound`; deliberate `sorry` and extra-axiom controls are
rejected. No `native_decide` or assumed hash evaluation is used to prove C6.
The evidence directory `evidence/2026-09-27/` records command outputs.

From the repository root, with pinned dependencies installed in `tooling/`
(or substitute the stable cache path above):

```sh
python3 formal/tools/r1cs_artifact.py --reproduce tooling/node_modules
python3 -m unittest discover -s formal/tools -p 'test_*.py' -v
node formal/tools/crosscheck_r1cs.cjs tooling/node_modules build/spend.r1cs formal/Artifacts/spend.manifest.json
python3 formal/tools/r1cs_artifact.py --check-lean formal/Artifacts/Spend.lean
python3 formal/tools/compression_fragment.py
python3 formal/tools/range_fragment.py
python3 formal/Poseidon/generate.py --check --node-modules tooling/node_modules
cd formal
lake build
python3 Poseidon/check.py --node-modules ../tooling/node_modules
```

The final full build passed 3,171 jobs with the new range theorem included in
the aggregate admission audit. Exact R1CS recompilation, all twelve parser and
fragment tests, full-data and fragment regeneration,
independent decoding, constant generation and 202 Poseidon comparisons passed.
These parser and differential tests are not the spec's semantic mutation gates.

## Remaining obligations and next action

First inspect Claude's new round-13 findings and key/verifier task before
assigning overlapping work. The concrete circuit frontier is to derive the
remaining five 128-bit range bounds from the actual optimized constraints
(reuse `Range.lean` and `RangeLemmas.lean`), prove beta and
all Poseidon gadget bindings, reconstruct eliminated signals, then bind
`Assignment`/`Satisfied`/projections and prove both C1 and C1c. Reference
Poseidon is concrete, but optimized sparse-round circuit equivalence is not
proved by the differential tests.

C2/C2c/C8/C9/C10 and refinement still need one faithful chain semantics, real
bytecode, custom instructions and both gas dimensions. W1/W2 and required
semantic mutation failures remain open. Keep the spec's cryptographic,
deployment, fork and lifetime premises; do not add the excluded privacy,
wallet, inclusion or fee-economics requirements.

A read-only feasibility check of EVMYulLean at
`047f63070309f436b66c61e276ab3b6d1169265a` found real bytecode execution
semantics, but its Lean 4.22 toolchain differs from this project's 4.35.0-rc3.
It lacks FrameTx/custom opcode support and two-dimensional gas. Its runtime
pairing and Keccak interfaces are not automatically kernel proofs. A possible
pilot is the pinned dispatcher runtime's first `TXPARAM` at PC 52, followed
by the sender-mismatch revert path; no such pilot has been implemented and it
would not alone prove approval-to-settlement. Do not silently replace concrete
chain obligations with trusted mocks.
