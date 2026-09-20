# Security

## Status

Unaudited research software. Do not use the committed proving key or deployed
testnet pool for real value. The repository setup is single-party, so its toxic
waste could forge arbitrary spends.

The previously identified implementation blockers are fixed in the active
code: complete-envelope authorization, positional sinks, pre-insert epoch
rollover, separate root publication, canonical Groth16 encodings, direct-call
rejection, exact spend framing, and EIP-7843 slot handling. Production
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
sponsorship or caller-selected fee recipient.

The circuit selects a fresh nonzero secp256k1 authorizer. EIP-8141 validates
its canonical low-s signature over the complete FrameTx hash. The dispatcher
requires that recovered signer through `SIGPARAM`, one signature, one exact
three-frame transfer or four-frame withdrawal grammar, the complete two-key
EIP-8250 nonce set, and the exact EIP-8272 tuple proven by the leading recent-root verifier frame. A copied or
rerandomized proof cannot be rewrapped without the one-time private key.

Payment approval consumes the EIP-8250 keys before SENDER settlement. Safety
therefore requires settlement to be total for every proof-valid admitted
transaction under the pinned fork gas profile. Settlement contains no
recipient calls. Its required Poseidon operations use fixed-code
static calls to two immutable, deployment-verified libraries. The settlement
budgets must be re-proved before every gas repricing fork.

Settlement is not yet total for every admitted proof-valid transaction. A
positive output commitment may already be in the tree, including one that a
recipient pre-shields after the sender signs. Approval then consumes the input
nonce keys before settlement rejects the duplicate output, so the promised
outputs and withdrawal credit are not created. The native suite reproduces
this existing baseline flaw. It remains a production blocker. The fourth frame
preserves credit after a successful settlement; it cannot recover a settlement
that failed.

The active tree rolls before any non-sink insertion when the current epoch
lacks capacity. Final roots remain authenticated by pool state. EIP-8272 source
IDs are distinct per epoch, preventing same-slot historical-publication
contention. Nullifiers use a stable chain-and-pool domain and never include the
epoch, so rollover cannot make an old note spendable twice.

Two distinct position-specific zero commitments represent no-output slots.
They are never inserted. Positive outputs cannot use either reserved inner,
the two output commitments must differ, and a spend must consume positive
private value. A full-tree withdrawal therefore creates only a pull credit and
does not roll or insert.

Root publication is not part of settlement. `publishEpochRoot(epoch)` accepts
no caller-supplied root, reads the active or finalized authenticated root, and
may safely be retried. A publication failure cannot consume note keys.
Withdrawals use checks-effects-interactions; a failed claim reverts and restores
the credit.

The Solidity implementation rejects direct state-changing calls. The immutable
dispatcher owns funds and storage. Deployment verifies the verifier,
dispatcher, logic, and both Poseidon runtimes before the pool is used.

## Recipient account requirements

The withdrawal frame is separate from settlement and must use `DEFAULT`, zero
value, and zero flags. It can call the exact pool claim or the proof-bound
recipient within explicit gas and calldata limits. It cannot add a `SENDER`
call or join settlement in an atomic batch. Tail failure leaves the settled
credit intact; it is not a failed settlement or a lost withdrawal.

The recipient authenticates its own request and binds it to the account,
chain, pool, specific settlement, action, value, and replay protection. The
test account signs the full settlement tuple, including its nullifiers, and
consumes its nonce before making external calls. It claims accumulated credit
but spends only the authorized value.

Before acting, the account checks the immediate caller is `address(0xaa)`, the
transaction sender is the trusted pool, the current frame index is 3, its
target is the account, and `FRAMEPARAM(2, 0x05) == 1`. Indices are zero-based.
The trusted dispatcher enforces the rest of the frame grammar. Without the
settlement-success check, a failed withdrawal could be followed by an action
funded from old credit. Nested calls inherit introspection, so frame context
alone does not establish authority or prevent reentry.

The account propagates claim or action failure so both roll back together.
The pool claim continues to send empty calldata. Adding arbitrary calldata to
that payment would let a note owner invoke recipient code with the pool as
the caller.

The account signature in calldata signs a separate request digest. It cannot
sign the complete FrameTx hash containing those same signature bytes. The
pool's existing outer signature binds the finished transaction, including the
account request and its authorization.

The dispatcher does not certify recipient code. An empty address or a fallback
that accepts calldata may report success without claiming. Wallets must select
a supported account explicitly; code presence alone is not a compatibility
check. The account's ordinary recovery path must remain able to claim credit
if the fourth frame fails.

The native integration suite executes the real dispatcher and proof with an
authenticated test account and a local Uniswap V2 market. It checks successful
swaps, rollback, credit recovery, independent account authorization, replay,
and both gas dimensions. This is evidence for that account and action under
the pinned client; it does not certify arbitrary recipient code.

## Assumptions and remaining gates

- Groth16 soundness, BN254 pairing security, Poseidon collision resistance,
  Keccak collision resistance, and secp256k1 unforgeability.
- A production multi-party phase-2 ceremony with destroyed contributions and
  independent transcript verification.
- Correct ethrex v23 implementations of EIP-8141, EIP-8250, EIP-8272 and
  EIP-7843 at the pins the activation manifest records.
- An explicitly supported verification budget of at least 352,800 gas: the
  recent-root verifier frame's 30,000, the proof frame's 320,000, and 2,800 for
  the signature. The published EIP-8141 public-mempool value is 100,000 and is
  insufficient.
- A fork-scoped proof that the settlement limits cover all cold-state, rollover,
  credit, proxy, and static-call paths. The current profile declares 1,400,000
  execution gas and 550,000 state gas, replacing the single 2,000,000-gas budget
  that predates EIP-8037's second dimension. Unsupported repricing forks require
  a new immutable profile.
- A fix for the duplicate-output race described above, so every admitted
  proof-valid transaction either settles or fails before its nonce keys are
  consumed.
- Independent circuit, Solidity, Yul, wallet, and deployment review.

EIP-8369 remains an open Informational proposal. Its current `2^20` per-IL
budget is provisional and does not activate or guarantee a per-transaction
limit. Hegotá's configured Profile 2 behavior is testnet evidence only.

The proving compiler and snark tooling remain pinned to the committed artifact
provenance. Transitive packages are overridden to patched versions where this
does not change circuit outputs. A direct compiler upgrade requires a new
artifact set, ceremony, activation manifest, and circuit review.

The wallet is a fixture generator, not a production keystore. Random note
secrets and one-time authorizer keys are not durably backed up.

## Evidence

The Forge suite covers actual Poseidon runtimes, a 2M-capped worst-shape
rollover with two outputs and a new credit, pre-insert rollover, full-tree
exit, sink rules, separate publication failure/retry, pull-credit failure,
direct-call rejection, valid proof verification, coordinate aliases, infinity,
and authorizer mutation. The circuit generator rejects same-note inputs,
duplicate outputs, dummy-only spends, wrong sinks, sink-valued positive outputs,
zero authorizers, and recipient mismatches. The envelope vector mutates 42
signed components.

The gas derivation is recorded in
[`devnet/vectors/2026-08-14-tight-gas-profile.md`](devnet/vectors/2026-08-14-tight-gas-profile.md).

The 2026-08-14 ethrex run completed shield, transfer, root refresh, withdrawal,
claim, and replay rejection. It proves compatibility with that one testnet
configuration, not production readiness or cross-client interoperability.

## Reporting

Report vulnerabilities privately to the repository owner before opening a
public issue. Include the affected commit, a minimal reproduction, impact, and
proposed mitigation. Do not test public deployments without permission.
