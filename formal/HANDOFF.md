# MSP formal verification continuation

## Ownership transfer, 2026-09-27 05:52 UTC

Thomas asked the Claude session `e9529fa7-10f6-4fd3-a0b1-195641fd261d` to
continue this work from Codex's committed state. Claude now owns the
specification and proofs, working in the worktree
`/Volumes/PrivateAI/WorkRepos/HardnessVault/prototypes/msp-formal-claude`
on branch `claude/formal-spec-continued`, started from `411f952`. Codex's
uncommitted files in this checkout (the `Groth16/Subgroup*` and `Cardinality`
files, `Chain/`, `Mutations/`, the circuit-mutation tooling) were left untouched
and are not part of that branch. Codex should not start new edits here; commit
or park what is in flight and stop, and Claude will pick up committed work.

## Codex handoff checkpoint

Codex's remaining work is now saved at **`7f670d6`**, directly after `411f952`.
Claude can cherry-pick that commit into its active worktree when ready; Codex
has not modified the Claude worktree. All Codex subagents and owned build
processes have stopped, and ownership has been yielded. The automation was
found already **PAUSED** during this transfer and remains paused.

The checkpoint contains checked Fq²/twist groups, exact order-`p` proofs for
all eight pinned key points and the G1 base point, and a concrete dispatcher
sender-mismatch proof. The latter follows 24 actual instructions, returns
`e6d22e28`, consumes exactly 80 execution gas and preserves carried persistent
state, approvals and state gas. It is only the documented rejection path,
not the complete canonical chain binding. `Proofs/AxiomAudit.lean` audits all
these results using only standard Lean axioms.

**Final check:** from this checkout's `formal/`, `/opt/homebrew/bin/lake build`
passes **3,661 jobs**. `python3 tools/groth16_subgroups.py` reproduces all nine
traces; `python3 tools/dispatcher_pilot.py --check` reproduces the pinned byte
data. Exact output and focused review are in
`evidence/2026-09-27-0350/handoff-full-build.log` and `handoff-review.md`.

Four complete executable circuit counterexamples and their raw artifacts are
preserved in `evidence/2026-09-27-0350/circuit-mutations/`. They are not Lean
mutation certificates. `Mutations/Check.lean` is checked generic reflection;
`MembershipValues.lean.pending` and `MembershipPilot.lean.pending` preserve
the unfinished concrete proof, with the recursion-limit failure and next steps
in `Mutations/README.md`. `Groth16/Cardinality.lean.pending` preserves the
unfinished ambient G1 cardinality proof; its last check was stopped while
slow. These pending files are intentionally outside build targets, without
admissions or claims of success.

No new obligation is closed beyond the stated bounds. Pairing/verifier/library
binding, canonical chain execution/refinement, W2 and Lean semantic mutation
gates remain open. P3/P9 retain their explicit canonical status. Next owner
should incorporate the checked checkpoint, inspect fresh round-21 review
results, and resume one documented pending obligation without repeating C1,
C1c or W1.

## Active checkout

The durable independent repository is
`/Volumes/PrivateAI/WorkRepos/HardnessVault/prototypes/msp-formal-verification`,
branch `codex/formal-continuation`. The scheduled Codex task is
`01a0dfaf-821e-7a11-b764-8ceeeb320135`, automation
`continue-msp-formal-verification`.

At 03:50 UTC on September 27, Codex resumed after Claude's parent session and
all six round-21 reviewers stopped with HTTP 429 at 03:27 UTC. The original
checkout was clean at `57ad96b`. Its round-13 through round-20 specification
and model changes are merged here at `634bb62`. The incomplete round-21 work
has no final new findings. A duplicate C6 helper import noted there is already
fixed in this continuation.

The separate key/R1CS task finished on September 26. Its unmerged PR 24 commit
`5a36bfc` is preserved locally and cherry-picked here as `6735e3e`; no worker
still owns that work. The activation gate has since been strengthened to bind
the verifier-used JSON key fields to the zkey. It still reports `setup: partial`.

**Historical Codex ownership, before the 05:52 UTC transfer above:** this heartbeat owned the durable checkout.
C1 and C1c are proved for all 14,802 pinned constraints with only standard Lean
axioms, at `7c96e43` and `6618d0d`. The full build passed 3,563 jobs there.
Concrete Ethereum Keccak is now bound as `K`; the circuit, model, composition,
key/encoding libraries and automated axiom audit pass 3,574 jobs after that
change. Ten Keccak fixtures and eight independent tests pass. The exact key
coordinate checks and strict proof decoder pass six artifact tests.

At 05:13 UTC Claude explicitly paused after reading this handoff, leaving the
original checkout clean at `57ad96b`. Root owns integration and generic frame
encoding. Bounded subagents own W1's actual run and query support, numeric
Poseidon certificates, and numeric Keccak certificates respectively. W1 is now proved as `MSP.w1`, with no hypotheses and only standard axioms.
The full default build passes 3,639 jobs, including its automated axiom audit. Before taking ownership, inspect fresh
task status, relevant Claude log timestamps and actual proof processes.
A quota reset or resident parent process alone does not transfer ownership.
Do not edit files while another worker is making progress.

Original Claude session: `e9529fa7-10f6-4fd3-a0b1-195641fd261d`.
Original checkout:
`/private/tmp/claude-501/-Volumes-PrivateAI-WorkRepos-HardnessVault/e9529fa7-10f6-4fd3-a0b1-195641fd261d/scratchpad/msp-formal`.
The durable Git object store does not depend on that temporary checkout.

## Scope and checks

`SPEC.md` is the canonical functional-verification scope. Read
`Proofs/README.md` for proven claims; `Spec/Main.lean` states the completion
theorems. Abstract model proofs do not discharge concrete circuit or chain
semantics bindings. C1 and C1c are discharged; the chain half, W2 and the
required semantic mutation gates remain open. C6 is now discharged for
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
It was not regenerated. This preserves the pinned test setup without rerunning the ceremony. The original repository's `57ad96b` commit is
preserved locally as `refs/remotes/claude-checkpoint/formal-spec` for reconciliation.

## Work in this continuation

The unfinished round-12 event-decoding finding is fixed in `SPEC.md`,
`Spec/Evm.lean` and `Spec/System.lean`: function events must decode original
message calls entering the pool, before delegation, excluding VERIFY
execution. This prevents a dispatcher mutation from changing an input while
the model follows the changed input. The new mutation remains an obligation
for the concrete semantics, not a claimed executed test.

`Proofs/Composes.lean` proves `MSP.composes : Composes` from the unchanged
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
It does not assume containment or the desired polynomial. `BetaGates` now
checks all 153 retained beta S-boxes and every affine stage. `PublicSignals`
combines it with universal optimized/reference Poseidon10 equivalence to prove
both canonical beta and gamma outputs for the same concrete statement.
All 54 note/path hash instances now have kernel-checked S-box and affine
certificates. `NoteBindings.relation_of_pinned_hash_instances` connects them
to the entire relation. `CircuitSoundness.lean` proves `MSP.c1 : C1` with no
remaining hash or relation premise. `Spec/Circuit.lean` now defines the actual
assignment carrier, full satisfaction predicate and three projections. The
four wrappers are irreducible to keep unrelated model simplification bounded;
C1 explicitly unfolds them. The C1/C1c propositions are unchanged.

`Proofs/CircuitArithmetic.lean` proves integer conservation from field
conservation and the six value bounds. `Proofs/CircuitGadgets.lean` proves
Boolean, IsZero and Num2Bits helper lemmas using a kernel-checked BN254
primality certificate from pinned, attributed Apache-licensed upstream code.
These helpers do not by themselves bind the production gadgets.

The subsequent `Artifacts/Range.lean` proof closes the first input's actual
range gate: `Range.first_input_range` derives `(w 10).val < 2^128` solely from
`Spend.system.Satisfied w`. It proves all 127 retained bits Boolean, reconstructs
the eliminated top bit from the actual last constraint, checks the coefficient
identity in Lean's kernel, and proves full-system containment. `RangeAmounts.lean` now proves the other five bounds, including the eliminated
fee, and integer conservation. `RangeAddress` proves both address bounds.
`BasicGates`, `InputNonzero` and `SinkGates` bind R6, R7, R8 and the non-range
R9 conditions to their actual gates. `Witness`, `PathBits` and `PathIndex`
provide one concrete witness projection, both bounded indices and agreement of
all 40 Boolean path wires with the canonical Merkle index digits.
`PathGates` binds all 80 selectors and both root checks. The strengthened
`RelationFragments.relation_of_gadget_hashes` assembles the relation with only
individual note and path hash equations explicit as premises. The new
`SmallHashGatesComplete` and `NoteBindings` discharge those premises and are
consumed by C1. These results use only standard Lean axioms.

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

## Latest checked proof batch

`evidence/2026-09-27-0350/` contains target, axiom and test outputs.
The complete C1 target passes 3,325 jobs. The stable aggregate command
`lake build Spec Sanity Proofs Poseidon Primality Artifacts.CircuitSoundness Artifacts.PinnedRangeCompleteness Artifacts.InputCompleteness`
passes 3,334 jobs. The subsequent expanded stable-library build and axiom audit
pass 3,489 jobs, including every completed constructive component. The later complete
`lake build` passes 3,563 jobs with C1c in the standard-axiom audit. C1 depends only on
`propext`, `Classical.choice` and `Quot.sound`. All 83 current artifact tests
pass with the environment below; seven optimized-data provenance tests passed
in the preceding batch. All 54 small-hash affine certificate modules build.
An independently changed affine output certificate is rejected by Lean.

The artifact suite requires the exact reproduced symbol file:

```sh
MSP_NODE_MODULES=/Volumes/PrivateAI/WorkRepos/minimal-shielded-pool/tooling/node_modules \
MSP_SPEND_SYM=/private/tmp/msp-fv-r1cs-reproduce-20260927/spend.sym \
python3 -m unittest discover -s formal/tools -p 'test_*.py' -v
```

The activation gate rejects eight malformed/self-certified manifest cases,
two unpinned/wrong ptau cases and thirteen key/setup mutations. Its accepted
pinned testbed still reports partial setup verification. Exact regeneration
checks bind generated data to pinned compiler symbols and sources. Decoder,
fragment and finite-certificate mutations do not replace the specification's
required complete semantic mutation gates.

## Remaining obligations and next action

C1c is discharged in `Artifacts/CircuitCompleteness.lean`. Its explicit
assignment combines 59 independently checked components, preserving the shared
semantic boundary and exact projections. `Proofs/CircuitModel.lean` connects
the completed circuit/model proofs to `MainTheorem` and `ChainCorollary`,
with only the still-open chain obligations as arguments.

W1 is discharged in `Proofs/NonVacuityFixtureVerified.lean`. Its actual
shield/publish/tick/spend run pays one unit in gas and credits one unit for
withdrawal. C1c supplies the real assignment; exact public triples define
W1's ideal verifier/extractor. Membership-equivalent compact queries cover
the whole original trace, and all 80 table entries have kernel-checked values,
uniqueness and nondegeneracy. No global hash assumption is used for this run.
The full default build passes 3,639 jobs. W2 remains open.

`Keccak/` defines the concrete reference bound by `Spec.Hash.K`, checkpoint
`d43388d`, with legacy padding, 24 rounds and big-endian digest output.
It is not yet a proof of the EVM/client hash implementation. `Groth16/`
binds exact pinned key coordinates and strict 256-byte decoding, including
EIP-197's G2 ordering. `Primality/BN254Base.lean` proves q prime; `Group.lean`
connects actual G1 coordinates to Mathlib's proved elliptic-curve group.
Quadratic-field/twist/subgroup/pairing and deployed-verifier bindings remain open.

Current subagents own a reproducible four-case circuit semantic mutation check,
quadratic-field/twist foundations, and a read-only faithful EVMYulLean port
review. Root owns integration. Mutation evaluations must be distinguished
from completed Lean counterexample certificates. Upstream EVMYulLean lacks
MSP custom instructions and currently defaults an undecoded opcode to STOP;
that must be fixed before claiming any dispatcher execution binding.

P3 setup honesty and P9 key/R1CS consistency are explicit canonical premises.
The activation gate's partial setup result and missing original powers-of-tau
file do not add an external blocker or a new requirement to the conditional
verification goal. Keep the gate's precise report, while continuing the actual
key/pairing/verifier semantics binding.

C2/C2c/C8/C9/C10 and refinement still need one faithful chain semantics, real
bytecode, custom instructions and both gas dimensions. W2 and required
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
