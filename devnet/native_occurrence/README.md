# Native occurrence tests

These tests execute real Groth16 proofs and signed frame transactions in the
native LEVM from ethrex `247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e`. They deploy
the contracts from this checkout and check frame results, nonce keys, tree
storage, withdrawal credits, recipient balances and gas payments.

Run after installing the repository's Python, Node, Foundry and Rust dependencies:

```sh
ETHREX_SOURCE=/path/to/pinned/ethrex python3 devnet/native_occurrence/run.py
```

Add `--offline` when Cargo dependencies are cached. `--skip-generate` reuses
locally generated vectors; a normal run recompiles contracts and regenerates
vectors. Cached proofs are keyed by their witness, proving key and circuit
WASM. No setup ceremony runs here. The repository's proving key is test-only.
Generated vectors and proof files are ignored by Git; the reports are kept.

The recorded run passes 67 native scenarios and two client-policy tests, using
32 real Groth16 proofs. The highest measured settlement execution cost is
1,423,709 gas (long carry plus withdrawal credit). The conservative five-slot
state test uses 489,600 state gas, below the 550,000 cap. The reports contain
each transaction hash and per-frame results.

The scenarios cover both copies of identical funded deposits being withdrawn
in one history, an identical private output and its original both being spent,
replay against a later root and slot, epoch/domain changes, and failed recipient
calls retaining their credit. Rejected transactions must leave the complete
EVM account state unchanged, including nonce keys and balances.

Fifteen scenarios cover the optional fourth frame. A withdrawal without a
tail keeps its credit, and a withdrawal or transfer may end with a generic
call to another account. A transfer may also call the pool. In one scenario it
publishes its own root, and the note it created is withdrawn against that root
in the next slot. When that publication fails, the settlement stands, and a
separate publication makes the note spendable. After a rollover, the tail must
publish the new epoch: doing so lets the output be withdrawn in the next slot,
while publishing the old epoch succeeds without the output until the new epoch
is published separately. Two tails call the pool to repeat the settlement or
the proof check, with enough gas to finish either; both revert, and the
settlement stands with each key consumed once. Each rejected case breaks one
rule of an otherwise valid spend and must fail in the pool's `VERIFY` frame: a
`SENDER` tail repeating the settlement, a zero target, an approval flag on the
tail, an atomic batch joining settlement and tail, and a fifth frame. A tail
carrying value is rejected statically by the client, as EIP-8141 requires,
before the dispatcher's own value check runs. Removing the dispatcher's mode
check lets the repeated settlement through with twice the proven credit, which
this suite then reports as a failure.

Seven scenarios cover the validation frames' limits, which the dispatcher no
longer pins. A withdrawal declaring far more than the defaults is accepted.
Declaring less than the recent-root frame's execution, the proof frame's
execution or the proof frame's state gas needs makes the transaction invalid in
that frame, with state unchanged. At a price where the default limits just fit
the proof's fee, the same withdrawal is accepted; raising the recent-root
frame's execution limit or the proof frame's state limit then pushes the
maximum cost past the fee, and the pool refuses it before approval, again with
state unchanged.

Nineteen scenarios cover hybrid compression, and each leaves state unchanged.
Twelve change one thing in a withdrawal: its `beta`, or one of the ten
statement values in the settlement calldata. For `nf1` and `nf2` the nonce keys
follow, and the authorizer case re-signs someone else's proof with an
attacker's key, so these reach the proof check along with the output, amount,
fee and recipient cases. The root and domain changes are refused earlier by the
exact tuple and domain checks, and a `beta` outside the field by both the
dispatcher and the verifier. Seven more prove an honest withdrawal against
`alpha` over one value plus the field modulus, so the proof and `gamma` pass
and only the dispatcher's range checks can refuse it. Deleting those checks
makes exactly these seven fail.

Six scenarios cover dispatcher checks that stop theft or a burn and that no
other scenario reaches. A spent key set replayed at `nonce_seq` 1 would pay out
again. The victim's signature, re-sent as an explicit message in a transaction
with another fourth frame, is valid under EIP-8141, and so is the attacker's
own signature over the victim's proof. A `DEFAULT` settlement frame
would revert after approval and leave the inputs spent. A recent-root frame sent
to the identity precompile echoes any tuple, including the root of an
attacker's own tree holding a note nobody deposited. The pool refuses each in
its `VERIFY` frame, and deleting any one of the five checks makes exactly its
scenarios fail.

The reorg scenario checkpoints the EVM database, executes and spends on one
branch, restores the checkpoint, and reverses two deposit transactions. The
old proof fails both with its old root and when rebound to the new root. A
rebuilt proof for the new position succeeds. This tests application recovery
under database rollback, not consensus fork choice or network reorganization.

Large-tree tests seed the exact frontier and balance of repeated funded
deposits, then execute proof verification and settlement normally. They cover
the longest carry, nearly full and full tree rollover, and spending a newly
created output from the rolled epoch. They do not execute a million deposit
transactions. Two additional tests inject conservative storage-bound states
(an empty active epoch and a zero frontier); those states are not claimed to
have been reached by deposits.

The settlement profile allows 2,000,000 execution gas and 550,000 state gas.
The old-limit regression deploys a separate dispatcher with only the pinned
settlement limit changed back to 1.4 million. It requires settlement to fail
after the nonce keys are consumed. The same long carry must settle successfully
under the new profile. Both execution and state gas are checked against each
frame's declared limits.

`policy/` runs the real validation observer, Profile 2 checks and direct client
mempool insertion with two independently signed, disjoint spends. It requires
zero sender-storage reads and both transactions to remain pending, and includes
storage-read and overlapping-key negative controls. This is not a test of full
blockchain admission, inclusion-list omission processing, block import or
networking. The 235,800 declared validation budget still exceeds the standard
100,000 public-mempool default and requires the existing testnet profile.
