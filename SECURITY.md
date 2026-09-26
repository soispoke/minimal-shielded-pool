# Security

## Status

Unaudited research software. Do not use the committed proving key or deployed
testnet pool for real value. The committed key comes from a local test setup.
Its phase 2 records one contribution, and its phase 1 is not recorded:
`tooling/setup.sh` generates both phases locally unless given an external powers
of tau. Whoever produced either phase could have kept the toxic waste and could
forge arbitrary spends.

The previously identified implementation blockers are fixed in the active
code: complete-envelope authorization, positional sinks, pre-insert epoch
rollover, separate root publication, canonical Groth16 encodings, direct-call
rejection, exact three/four-frame self-payment, and EIP-7843 slot handling. Production
activation remains blocked on a real ceremony, independent audit, cross-client
evidence, and fork-specific gas proof.

The active transaction encoder and dispatcher target EIP-8141 as currently
specified: nested fees and separate execution and state gas limits. The
pre-relaunch Hegotá testnet profile they previously targeted is archived under
`devnet/vectors/2026-09-01-hegota-final-profile/` and is not usable against any
live network. A client
upgrade to that format requires a new immutable pool profile and deployment.

## Security model

The pool holds native ETH. Notes, fees, withdrawals, and payer costs are all
wei-denominated. The pool is the EIP-8141 sender and payer. There is no
external paymaster or caller-selected fee recipient.

The wallet chooses a fresh secp256k1 authorizer for each spend, and the
circuit requires it to be nonzero. EIP-8141 validates
its canonical low-s signature over the complete FrameTx hash. The dispatcher
requires that recovered signer through `SIGPARAM`, one signature, a three- or
four-frame spend grammar, the complete two-key
EIP-8250 nonce set, and the exact EIP-8272 tuple proven by the leading
recent-root verifier frame. A copied or rerandomized proof cannot be rewrapped
without the one-time private key.

The proof exposes three public signals instead of the ten statement values,
using the hybrid compression of eprint 2025/1500. The ten values stay public in
the settlement calldata; only the verifier's inputs shrink. Binding the
statement to the proof therefore rests on the paper's joint UHF hardness of
Keccak-mod-p and Poseidon, as well as on Groth16. The dispatcher recomputes
`alpha` and `gamma` from the settlement calldata and range-checks each
statement value before the verifier runs. Those range checks are
load-bearing. Without them, the note owner could re-prove a spend with a value
plus the field modulus in the calldata: `alpha` changes, but `gamma` reduces
the value to the same field element, so VERIFY approves under different
nonce keys. Settlement re-checks the values and reverts after approval, so the
pool pays the gas each time, and an aliased output, amount or fee spends the
input notes without creating anything.

Payment approval consumes the EIP-8250 keys before SENDER settlement. Safety
therefore requires settlement to be total for every proof-valid admitted
transaction under the pinned fork gas profile. Previously, a duplicate output
could revert settlement after consuming the input keys. Position-bound
nullifiers let settlement append that separately funded occurrence instead.
This removes the duplicate failure path; arbitrary post-approval failures
remain unsafe, so the supported settlement gas bounds are still load-bearing.
A failed tail frame does not undo settlement. If a withdrawal tail reverts or
runs out of gas, the credit created by frame 2 remains on `recipient` and can
be claimed later. The optional generic tail is outside settlement's failure
scope. The proof-bound fee must cover the complete transaction's maximum
cost. The wallet allocates any tail inside remaining EIP-7825 execution
capacity and the chain's transaction size limits; the dispatcher does not
add a pool-specific tail gas or calldata ceiling. Required Poseidon
operations use fixed-code
static calls to two immutable, deployment-verified libraries. Settlement
execution is pinned at 2M because 1.4M OOGs long-carry after approval;
that 2M execution and 550k state budgets must be re-proved before every
gas repricing fork.

The active tree rolls before any non-sink insertion when the current epoch
lacks capacity. Final roots remain authenticated by pool state. EIP-8272 source
IDs are distinct per epoch, preventing same-slot historical-publication
contention. Nullifiers bind chain, pool, the authenticated input epoch, the
commitment and its constrained Merkle index. They never use the changing root,
publication slot or current output epoch, so rollover and republication cannot
make an old occurrence spendable twice. Zero-value dummy inputs retain the
commitment binding, preventing them from copying a funded note's nullifier.

This is a fresh-deployment change. Reusing an old pool's spent-note state with
the new nullifier formula could permit double spending. The versioned profile
rejects historical deployment configs. Wallets must retain duplicate
commitments as distinct occurrences and rebuild canonical positions and spend
IDs after a reorg. Native tests simulate removed and replacement state; they
do not implement consensus fork choice or a production wallet database.

Two distinct position-specific zero commitments represent no-output slots.
They are never inserted. Positive outputs cannot use either reserved inner,
the two output commitments must differ, and a spend must consume positive
private value. A full-tree withdrawal therefore creates only a pull credit and
does not roll or insert.

Root publication is not part of settlement. `publishEpochRoot(epoch)` accepts
no caller-supplied root, reads the active or finalized authenticated root, and
may safely be retried. A publication failure cannot consume note keys. A
transfer may publish from its tail, after settlement. It must name the epoch
its outputs landed in: after a rollover, publishing the old epoch succeeds but
leaves the new notes unpublished. If the tail's publication fails or names the
wrong epoch, retry only the publication, because settlement has already
consumed the input notes. Under EIP-8272, a later publication for the same
epoch in the same slot replaces the stored root. The replacement still
contains the notes, but proofs must use the root stored last.
Withdrawals use checks-effects-interactions; a failed claim reverts and restores
the credit.

The Solidity implementation rejects direct state-changing calls. The immutable
dispatcher owns funds and storage. Deployment verifies the verifier,
dispatcher, logic, and both Poseidon runtimes before the pool is used.

## Generic DEFAULT tail

A spend may append one `DEFAULT` frame whose target and calldata are chosen by
the note authorizer and bound by the complete transaction signature. The frame
has zero value and flags and cannot target the zero address. The dispatcher
does not pin tail execution, state gas, or calldata. The wallet allocates the
requested budget inside remaining transaction capacity: EIP-7825's `2^24`
execution cap covers intrinsic gas, every frame's execution budget, and the
EIP-7976 calldata floor. State gas is accounted separately; native testing
admitted 10M execution plus 10M state. The pinned ethrex client applies a
128 KiB mempool limit to the entire encoded transaction, not to the tail
alone. Wallets default the tail to the old `claimWithdrawal` budgets (100,000
execution / 183,600 state) and only raise gas for a custom target or
calldata. Both pinned ethrex revisions panic executing a top-level frame to a
precompile after an earlier frame emitted logs, which settlement always does.
Mempool admission runs only the validation prefix, and the payload builder
does not catch the panic on its first build, so one such pending transaction,
from any wallet and not only a pool spend, stops an ethrex node from producing
blocks until it leaves the mempool. The CLI refuses precompile targets; the
pool cannot stop another wallet from sending one, and the fix belongs in
ethrex. Settlement remains the
only `SENDER` frame. The fourth frame is optional on every spend, including
withdrawals: omitting it leaves `withdrawalCredit`. Any tail may call the
pool, but it can only do what any caller can: publish a root with
`publishEpochRoot`, pay out a credit with `claimWithdrawal`, or read state.
`settle` accepts only the pool itself as caller, `shield` needs ETH, and the
pool's `VERIFY` entry works only in frame 1. A tail that tries to repeat
settlement or verification therefore reverts on its own, and the settlement
stands.

`recipient` is the payout key, not the frame target. `claimWithdrawal(who)`
always pays `who`. Anyone can still call `claimWithdrawal` later. The authorizer
does not have to pull the credit in the tail; a later standalone claim remains.

Credits are one balance per recipient address. Withdrawals to the same account
accumulate, and anyone can push the whole balance to it at any time, so an
account shared by several users must not attribute a claimed balance change to
one withdrawal. The wallet refuses the pool itself and known protocol addresses
that would strand the credit: the EIP-8141 entry point and expiry verifier, the
EIP-8250 nonce manager, the EIP-8272 recent root contract, the EIP-4788,
EIP-2935, EIP-7002 and EIP-7251 system contracts, the beacon deposit contract,
the EIP-8282 builder deposit and exit contracts, and precompiles. Any other
contract that rejects a plain ETH transfer strands a credit the same way.

The account sees EIP-8141's shared entry point (`0xaa`) as its caller, not
the pool or the account owner. Trusting that caller alone would let any frame
transaction operate the account. The account must independently authenticate
its owner's action and prevent replay. The pool's proof-selected authorizer
only authorizes spending the shielded notes and paying gas.

A wallet must select an execution path compatible with this call. Supporting
EIP-8141, EIP-7702 or ERC-4337 does not by itself establish compatibility.

After successful settlement, a failed tail still spends the input notes
and pays fees; private change outputs and any withdrawal credit remain. The
wallet must inspect the individual frame receipts and must not retry the
consumed spend. An independently submitted account signature may execute
before the pool transaction unless its authorization also binds the intended
execution context.

The existing settlement-failure blocker above is unchanged. An account that
requires settlement to succeed must verify that status before acting. This
extension neither repairs that blocker nor provides full-spend atomicity.

## Privacy limits

The proof hides which notes a spend consumes. The rest of the statement is
public calldata, and these patterns can still link a spend to a deposit or to
other spends:

- A spend whose two outputs are both sinks creates no private output, so its
  inputs total exactly `publicAmount + fee`. A full withdrawal of a note with
  an unusual amount is then linked to that deposit. A change output hides the
  total.
- An output commitment is `Poseidon(2, inner, value)`, with no randomness
  beyond `inner`. Anyone who knows an `inner` can test amounts against it, so
  a wallet must use a fresh `inner` for every payment and never publish one as
  an address.
- A spend names the slot of the root it proves against, and root publication
  is an ordinary transaction. Publishing that root from the depositor's
  account, or from a spend's fourth frame, links the later spend to that
  account or that spend. Prove against a root someone else published, or
  publish from an unrelated account.
- The authorizer is public. The wallet makes a fresh one for each spend;
  reusing one, or signing with a key tied to the depositor, links spends.
- A spend reveals its input epoch, so notes in different epochs never share an
  anonymity set. Anyone can force a new epoch by filling the tree: `2^20`
  deposits at about 0.8 million gas each, roughly 800 ETH at 1 gwei and almost
  nothing at the testnet's base fee.
- Fees, gas limits, fee caps and fourth-frame choices differ between wallets
  and make their spends recognizable.
- A disclosure receipt reveals the links and amounts it covers to whoever
  holds it, and they can pass it on. Disclosing both inputs of a spend and one
  output also reveals the other output's value by conservation. If that note
  is later withdrawn in full, the amount links the withdrawal to it, even when
  the note belongs to someone else. A nullifier key shows when any note of the
  same spend key is spent in that epoch, including another deposit of the
  same commitment, so the wallet makes a fresh spend key for each note. The
  receipt also reveals each note's `inner`, which links any other note paid to
  the same `inner`.

## Assumptions and remaining gates

- Groth16 knowledge soundness, BN254 pairing security, Poseidon collision
  resistance, Keccak collision resistance, and secp256k1 unforgeability.
- Joint UHF hardness of Keccak-mod-p and circomlib Poseidon(10), the
  assumption under which eprint 2025/1500 proves hybrid compression binds the
  ten statement values to the proof's three public signals.
- A production setup: a public multi-party phase 1, and a multi-party phase-2
  ceremony with destroyed contributions and independent transcript
  verification. The activation gate counts only phase-2 contributions, so
  phase-1 provenance must be checked separately.
- Correct ethrex v23 implementations of EIP-8141, EIP-8250, EIP-8272 and
  EIP-7843. The activation manifest records the EIP-8250 and EIP-8272
  revisions, and the native suite pins ethrex `247e2dd2`.
- An explicitly supported verification budget covering what wallets declare:
  235,800 gas by default, the recent-root frame's 8,000, the proof frame's
  225,000 and 2,800 for the signature. The dispatcher does not pin these two
  limits, so wallets can raise them after a repricing, up to the fixed 500,000
  gas the dispatcher forwards to the verifier. The published EIP-8141
  public-mempool value is 100,000 and is insufficient.
- A fork-scoped proof that the settlement limits cover all cold-state, rollover,
  credit, proxy, and static-call paths. The current profile declares 2,000,000
  execution gas and 550,000 state gas. Native testing on ethrex `247e2dd2`
  reproduced valid spends at 262,143 and 524,287 leaves where both VERIFY
  frames succeed, approval consumes the input keys, and settlement then fails
  at the previous 1,400,000 execution pin. Changing the dispatcher pin and
  signed frame limit to 2,000,000 makes those cases succeed; 2M is not by
  itself a proof of every settlement shape. Unsupported repricing forks
  require a new immutable profile. The pins cannot change and the pool has no
  migration path, so holders should exit before such a fork. Spends that
  insert outputs are the first to stop fitting; a full withdrawal to two sinks
  writes at most one new slot and fits unless the state price per slot rises
  more than fivefold.
- No chain that keeps this pool's state changes its chain ID, as the minority
  side of a contentious fork might. The nullifier domain uses the chain ID at
  spend time, so on such a chain every spent note gets a fresh nullifier and
  can be spent again, draining that chain's copy of the pool. A future profile
  could bind the deployment chain ID instead.
- Mempool policy that admits concurrent spends. Every spend has the pool as
  sender, so per-sender limits apply to all users at once. EIP-8141's
  conservative rule keeps one pending frame transaction per sender; both
  ethrex revisions relax it for spends with disjoint keys. The pinned
  revision's MATCHA, on by default, charges each pending spend beyond the
  first to one width budget for the pool, at admission and again at every
  forkchoiceUpdated, and evicts spends it can no longer pay for. The budget
  refills only from the pool's own finalized gas, so on a node that admits the
  pool's validation budget, a few concurrent spends, or one note holder
  replacing a spend while another is pending, can exhaust it and delay
  everyone else's. The live chain's client has no such budget. A wallet that raises a pending spend's fee beyond
  its proof's fee must re-prove with the same dummy input, since a new dummy
  changes the key set and the mempool refuses it while the first spend is
  pending.
- Client capacity for pending spends. Both ethrex revisions revalidate every
  pending spend, Groth16 pairing included, on each forkchoiceUpdated, at 1.1 to
  1.3 ms each on fast hardware. On the live client, which has no width budget,
  about 6,000 to 7,000 pending spends, fewer on slower nodes, would exceed the
  Engine API's 8-second limit. These limit liveness, not safety.
- Independent circuit, Solidity, Yul, wallet, and deployment review.

EIP-8369 is a Draft Informational EIP. Its current `2^20` per-IL
budget is provisional and does not activate or guarantee a per-transaction
limit. Hegotá's configured Profile 2 behavior is testnet evidence only.

The proving compiler and snark tooling remain pinned to the committed artifact
provenance. Transitive packages are overridden to patched versions where this
does not change circuit outputs. A direct compiler upgrade requires a new
artifact set, ceremony, activation manifest, and circuit review.

The wallet is a fixture generator, not a production keystore. Random note
secrets and one-time authorizer keys are not durably backed up. The fixture
generators' fixed seed is public, so they refuse it outside the local test
chain or a live tree, and refuse recipients that would strand a credit. A
fixture's proofs assume the tree its generator built, so another deposit
landing first leaves them unusable. Each spend entry therefore keeps its
inputs' openings, and the nonce-race transfers their outputs', from which the
notes can be proved again at the leaves they occupy. The generators write
secrets readable by their owner only, put live fixtures under the ignored
wallet/artifacts/, and never write over a fixture for another chain. Keep a
fixture as long as its notes are unspent.

## Evidence

The Forge suite runs the via-IR Poseidon builds, which cost about 10% less
gas per hash than the deployed `libsmall` builds, so the binding settlement
bound comes from the native suite below. The Forge suite covers a 2M-capped
rollover with two outputs and a new credit, long-carry at 262,143 and 524,287
leaves under EIP-150 forwarding of that 2M budget, pre-insert rollover, full-tree
exit, sink rules, separate publication failure/retry, pull-credit failure, a
reentrant recipient paid once, credits that accumulate, a root recomputed when
only the second output is new, the full tree's root kept when the last leaf
fills, direct-call rejection, valid proof verification, coordinate aliases, infinity,
and mutation of each statement value, `beta` and `gamma`. The circuit generator
rejects same-note inputs, duplicate outputs, dummy-only spends, wrong sinks,
sink-valued positive outputs, zero authorizers, and recipient mismatches. The
circuit test checks `beta` against an independent Poseidon(10) and rejects a
forged witness whose `beta` or `gamma` does not follow from the statement, and
witnesses that each break only one constraint: value conservation, the 128-bit
ranges of the fee and of each output, including an output of exactly 2^128,
path-bit booleanity at several depths, and the sink rules. Each rejection is checked against the committed R1CS, not
only the witness generator, using a complete witness from a circuit without
that constraint, so a constraint that became a runtime-only check would fail
the test. The circuit test also fails if the circuit gains an unconstrained
assignment (`<--` or `-->`), which it currently has none of. The
envelope vector checks that changing any of 49 transfer components, 57
withdrawal components, 58 gas-only tail components or 58 custom withdrawal tail
components, including `beta`, changes the signed hash.

The position-bound note suite passes 77 native scenarios using 32 real Groth16
proofs, plus two client-policy tests, against the current dispatcher. It covers
duplicate deposits and outputs, replay, epoch binding, database rollback and
proof rebuilding, settlement gas boundaries, the fourth-frame rules,
including a transfer that publishes its own root and rejection of a `SENDER`
tail that repeats settlement, the
unpinned validation limits, the fee check that covers them, and hybrid
compression, including fresh proofs over a statement value plus the field
modulus that only the dispatcher's range checks refuse, and malformed envelopes
that only the dispatcher's key, signature, settlement, recent-root and domain
checks refuse. The highest measured settlement execution cost is 1,423,709;
the old 1.4M limit fails after consuming input keys. The new 2M limit includes
additional margin, not a formal proof of a universal bound. These runs use
ethrex `247e2dd2`; the live chain runs `bdfc5d8f`, 88 commits older, where
the same scenarios give identical results, gas included. See
[`devnet/native_occurrence/README.md`](devnet/native_occurrence/README.md).

The earlier profile's gas derivation is recorded in
[`devnet/vectors/2026-08-14-tight-gas-profile.md`](devnet/vectors/2026-08-14-tight-gas-profile.md).

On 2026-09-25 the `position-notes-v2` pool recorded in
`devnet/deploy_config.json` (commit `08bb034`, block 143402) completed a
shield, two root publications, a transfer, a withdrawal whose fourth-frame
claim failed and left its credit, and a withdrawal whose fourth-frame claim
paid the recipient both credits, on the chain 8141 testnet.

On 2026-09-22 the previous profile, `position-notes-v1` at `c26b8e4`,
completed shield, transfer, root refresh, withdrawal, claim, a fourth-frame
claim and call, an intentional tail revert with later credit recovery, and
replay rejection on the same testnet. It predates hybrid compression, the
unpinned validation limits and pool-calling tails, and the current CLI refuses
it.

These runs prove compatibility with that one testnet configuration, not
production readiness or cross-client interoperability.

## Reporting

Report vulnerabilities privately to the repository owner before opening a
public issue. Include the affected commit, a minimal reproduction, impact, and
proposed mitigation. Do not test public deployments without permission.
