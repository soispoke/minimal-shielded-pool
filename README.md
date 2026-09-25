# Minimal shielded pool

> [!CAUTION]
> **This is a research prototype, not production software. Do not deploy it on
> mainnet or use it with real funds.**
>
> - **Whoever ran the trusted setup could steal everything in the pool.** The
>   committed Groth16 proving key comes from a local test setup. Whoever
>   produced either of its two phases could have kept the secret values and
>   could forge proofs that mint notes and drain the pool.
> - **No outside auditor has reviewed the contracts or the circuit.**
> - **It depends on draft EIPs.** EIP-8141, EIP-8250 and EIP-8272 are drafts
>   and are not live on mainnet. This version of the pool has run only in
>   local tests, and earlier versions only on test networks. Each change to the
>   drafts' transaction format needs a new pool.
> - **Nothing can be fixed after deployment.** The pool has no admin, upgrade,
>   pause or recovery path, so a bug or an adverse gas repricing cannot be
>   fixed in place.
> - **The wallet code is test tooling.** It builds notes, proofs and
>   transactions for tests, keeps note secrets only in unencrypted fixture
>   files and does not handle reorgs. The pool publishes only note
>   commitments, so payer and recipient must exchange note details off chain.
>
> See [What production would require](#what-production-would-require) and
> [SECURITY.md](SECURITY.md).

## What it is

The pool holds native ETH in private notes. A deposit, called a shield,
creates a note. A spend consumes one or two notes, creates up to two new ones
and can withdraw value to a public address. A zero-knowledge proof shows that
the spend is valid without revealing which notes it consumed.

It is built for the Hegotá testnet (chain ID 8141), which runs the ethrex
execution client, and uses three draft EIPs:

- **EIP-8141 frame transactions** let the pool send and pay for each spend,
  so spending needs no funded account once a recent root of the note tree
  that includes the note has been published.
- **EIP-8250 keyed nonces** let the pool use each nullifier, the value a spend
  reveals for each note it consumes, as a nonce key at sequence zero. The
  protocol accepts each key at sequence zero only once, so a note cannot be
  spent twice.
- **EIP-8272 recent roots** let the protocol check that the root a spend's
  proof uses was published recently.

It has no ERC-20 support, admin, governance or external paymaster.

## How it works

### Notes and nullifiers

A note commits to its owner, a random `rho` and its value:

```text
owner_pk = Poseidon3(1, spend_key, 0)
cm       = Poseidon3(2, Poseidon2(owner_pk, rho), value)
```

`PoseidonN` is circomlib's Poseidon hash over BN254 with N inputs, not the
separate Poseidon2 hash.

Notes go into a Merkle tree of 2^20 leaves. When a shield or spend needs
more room than the tree has left, the pool first starts a new tree, and the
trees are numbered by epoch. Every note, whether created by a shield or a
spend, is identified by its epoch and leaf index. The nullifier binds that
position, so two notes with the same commitment are spent independently and
no uniqueness registry is needed:

```text
D  = keccak256(domain_tag || chain_id || pool || epoch) mod r
nf = Poseidon3(4, Poseidon2(D, spend_key), Poseidon2(cm, leaf_index))
```

Here `domain_tag = keccak256("minimal-shielded-pool:occurrence-domain:v1")`,
each field is 32 bytes and `r` is the order of the BN254 scalar field. The
pool checks that `D`, which the spend carries publicly as `domain`, uses the
epoch of the root the spend proves against.
Otherwise a spender could prove a note against one epoch's root, derive its
nullifier from another epoch, and spend it twice. Wallets must track notes by
position and rebuild positions after a reorg.

### The proof

A spend proves a join-split with two inputs and two outputs, and a zero-value
placeholder fills any input or output the spend does not use. The circuit
checks that:

- each nullifier is computed from its input's spend key, commitment and leaf
  index, as in the formula above;
- every input with value is in the tree under the spend's single `root`, so
  all of them come from the same epoch;
- value is conserved, over 128-bit amounts;
- at least one input carries value;
- the two nullifiers differ, and so do the two outputs;
- the authorizer, a fresh signing key described below, has a nonzero address;
- a recipient is set exactly when `publicAmount` is positive;
- a zero-value output uses the fixed "sink" commitment for its position, which
  the pool never inserts.

The statement has ten values: `[nf1, nf2, outCm1, outCm2, root, domain,
publicAmount, fee, recipient, authorizer]`. To save verification gas, the proof
exposes only three public signals, `alpha`, `beta` and `gamma`, using the
hybrid compression of [eprint 2025/1500](https://eprint.iacr.org/2025/1500).
The pool computes `alpha = keccak256(statement) mod r`, the circuit computes
`beta`, a Poseidon hash of the ten values, and both compute `gamma`, the
statement as a polynomial evaluated at `alpha + beta`. The ten values stay
public in the settlement frame's data. Because the verifier no longer sees them, the
pool recomputes `alpha` and `gamma` from them and range-checks each value
itself.

### Transactions

An EIP-8141 transaction is a list of frames, each a call with its own mode and
gas limits. A `VERIFY` frame checks the transaction and can approve its
execution and payment, a `SENDER` frame calls its target from the
transaction's sender, and a `DEFAULT` frame calls it from EIP-8141's entry
point.

The pool is the sender and payer of every spend. The two nullifiers are the
transaction's EIP-8250 nonce keys at sequence zero. A spend has three frames
and an optional fourth:

1. `VERIFY(0x…8272, tuple)`: EIP-8272 checks that the `(source_id, slot,
   root)` tuple names a recently published root. `source_id` is derived from
   the pool and the epoch, and `slot` is the EIP-7843 `slotNumber` of the
   block that published the root. The proof covers the root and, through `D`,
   the epoch. The authorizer's signature covers the slot.
2. `VERIFY(pool, proof)`: the pool checks the proof, binds it to that tuple,
   and checks the frame layout and the settlement frame's gas limits. It then
   approves execution and payment.
3. `SENDER(pool, settle(Spend))`: settlement inserts the outputs and records
   any withdrawal as a credit for `recipient`. The approval in the proof frame
   has already consumed the nullifiers as nonce keys, so a failed settlement would
   burn the notes. Settlement therefore never publishes a root or calls the
   recipient, and the pool's `VERIFY` rejects anything settlement would
   refuse.
4. An optional `DEFAULT` frame that calls any nonzero target, including the
   pool, with any calldata, no value and no frame flags, so it cannot approve
   execution or payment. The CLI refuses precompile targets (see
   [SECURITY.md](SECURITY.md#generic-default-tail)). A withdrawal usually
   calls `claimWithdrawal(recipient)`. A transfer can call `publishEpochRoot`
   so the notes it creates can be spent from the next slot, though a spend
   against that root is then easy to link to the transfer. That call must name
   the epoch the new notes land in, which is a new epoch if settlement started
   a new tree. Naming the old epoch succeeds but leaves the new notes
   unpublished.

The proof names a secp256k1 authorizer, a fresh key the wallet makes for each
spend. Its signature covers the whole transaction, including the proof, the
recent-root tuple and the fourth frame. The proof's `fee` must cover the
transaction's maximum cost, and any unused part stays in the pool.

### Gas limits

| Frame | Execution gas | State gas | Data |
|---|---:|---:|---:|
| Recent root | 8,000 default (uses 5,579) | 0 pinned | 72 bytes |
| Proof | 225,000 default (uses about 210,000) | 195,840 default | 288 bytes |
| Settlement | 2,000,000 pinned | 550,000 pinned | 388 bytes |

The pool pins the data length of the first three frames and the settlement
frame's gas limits. Settlement must never run out of gas, since that would
burn the notes. The 2,000,000 execution limit leaves margin above the highest
cost the native tests measured (1,423,709), but a measurement is not a proof
that every tree shape fits, and a repricing that makes settlement more
expensive needs a new pool.

The validation frames' limits are wallet defaults, except the recent-root
frame's state limit, which EIP-8272 requires to be zero. A limit that is too
low only makes the transaction invalid, so wallets can raise these limits
after a repricing, as long as the proof check fits the 500,000 gas the pool
forwards to the verifier. Otherwise they should keep the defaults, since a
spend with different limits stands out. The proof frame needs about 216,000
execution gas although it uses about 210,000, because each nested call keeps
back 1/64 of its gas (EIP-150). Below that, the pool reports an invalid proof.
The frame's state gas pays for the two nullifier keys, and its data is the
256-byte proof followed by `beta`.

The wallet chooses the fourth frame's limits. Intrinsic gas plus every frame's
execution limit, or the calldata floor when larger, must fit EIP-7825's `2^24`
cap, of which the pool's frames use 2.23M by default. State gas is budgeted
separately. The encoded transaction must also fit ethrex's 128 KiB mempool
limit.

### After settlement

If the fourth frame fails or is left out, settlement still stands, and a
withdrawal remains as a credit that anyone can pay out later with
`claimWithdrawal(recipient)`. A failed fourth frame sets the receipt's overall
status to 0 even though settlement succeeded, so check each frame's status.
The claim pays `recipient` with a plain ETH transfer and cannot redirect it,
so a recipient that rejects plain ETH transfers strands the credit.

An account called by the fourth frame sees EIP-8141's entry point as its
caller, not the pool or the account's owner. Any frame transaction can make
that call, so the account must authenticate its owner's action itself and
prevent replay. Supporting EIP-8141, EIP-7702 or ERC-4337 does not by itself
make an account compatible. See [SECURITY.md](SECURITY.md#generic-default-tail).

Sinks take no space, so withdrawing a note's full value from a full tree
inserts nothing and needs no new epoch. Anyone may publish the current epoch's
root, or the final root of any earlier epoch, to EIP-8272.

## Code

| Path | Contents |
|---|---|
| `circuits/spend.circom` | The spend circuit |
| `devnet/ShieldedPoolDispatcher.yul` | The pool contract. It holds the funds and storage, checks each spend's frames and proof, and delegates every other call, including settlement, to the logic contract |
| `contracts/src/ShieldedPoolLogic.sol` | Shielding, settlement, the note tree, root publication, withdrawal credits and claims |
| `contracts/src/Groth16Verifier.sol` | The verifier generated for the test proving key |
| `contracts/src/PoseidonT3.sol`, `PoseidonT4.sol` | Poseidon hash libraries |
| `devnet/dispatcher.py` | Builds the pool's bytecode |
| `devnet/pool_frametx.py` | Command-line tool (the CLI) that shields, publishes roots and sends spends |
| `devnet/run_live_dispatcher.sh` | Test deployment script for chain 8141. It requires `ALLOW_TESTBED_SETUP=1` to acknowledge the test proving key |
| `wallet/wallet.py` | Note, nullifier, tree and witness helpers |
| `wallet/gen_smoke.py` | Generates proof fixtures for tests and test deployments |

## Profiles and deployments

This is pool profile `position-notes-v2`, for EIP-8141 at `7d1c8bfb94`,
EIP-8250 at `f3079a09e8` and EIP-8272 at `824cbc0b0e`. Under these versions a
frame transaction has eight top-level fields, and each frame declares separate
execution and state gas limits. A profile fixes both the draft versions and
the pool's code. Spends built for one profile fail against another profile's
pool, so each profile needs its own deployment, since a deployed pool cannot
be upgraded. The format the Hegotá
testnet used before its relaunch is archived under
`devnet/vectors/2026-09-01-hegota-final-profile/`.

No `position-notes-v2` pool has been deployed yet. `devnet/deploy_config.json`
still records the earlier `position-notes-v1` pool on the Hegotá testnet
(`0xac01…b100`, commit `c26b8e4`), which completed shield, transfer,
withdrawal and fourth-frame calls on September 22, 2026. That pool rejects
this profile's validation limits, and the CLI refuses to shield into or spend
from it.

Before shielding or spending, the CLI checks that the config names this
profile, that the RPC is on the configured chain, that the pool's code is
exactly what this profile deploys with the configured logic and verifier, that
its `domain(uint64)` matches, and that the verifier accepts a reference proof
and rejects it with `gamma` changed. These checks catch a stale or mislabeled
config, not a malicious deployer. They trust the configured logic and verifier
and cannot see what a constructor wrote to storage, so check the deployment
transactions of any pool someone else deployed before depositing into it.

A shield also refuses a fixture made for another chain, pool or epoch, or one
whose proofs expect a different next leaf or tree than the pool has. If
another deposit lands first, the CLI reports where the note landed, and the
note must be proved again at that leaf from the opening in the fixture, so
keep a fixture until its notes are spent. Before sending, and with
`--dry-run`, the CLI gives the RPC the fully signed transaction to simulate,
and the RPC could broadcast it. Use an RPC you trust.

The public mempool counts a spend's declared validation gas, 235,800 by
default including 2,800 for the signature, although a spend uses about
218,500. Both exceed EIP-8141's published default budget of 100,000, and
[EIP-8369](https://eips.ethereum.org/EIPS/eip-8369) has not settled a
per-transaction budget. Every spend also has the pool as its sender, and
EIP-8141's conservative rule keeps one pending frame transaction per sender,
which would mean one pending spend across all users. The Hegotá testnet's
ethrex client admits up to 500,000 validation gas and relaxes the sender rule
for spends that share no nonce key. Other networks need a policy that does both.

## Tests

```sh
npm ci --prefix tooling
python3 -m pip install --requirement requirements.txt

python3 devnet/frametx.py
python3 devnet/test_pool_envelope_binding.py
python3 devnet/test_gas_only_action.py
python3 devnet/test_recent_root_window.py
python3 devnet/test_occurrence_profile.py
python3 devnet/test_deploy_checks.py
python3 wallet/test_occurrence.py
python3 wallet/test_wallet_occurrence.py
python3 wallet/test_generators.py
python3 tooling/check_gas_profile.py
python3 tooling/check_activation.py activation_manifest.testbed.json --allow-testbed
python3 tooling/check_forge_config.py activation_manifest.testbed.json contracts
python3 tooling/test_check_activation.py
python3 wallet/wallet.py
python3 reference/poseidon_bn254.py

forge fmt --root contracts --check
forge lint --root contracts --deny warnings
forge test --root contracts --force -vv
```

CI also rebuilds the circuit and requires byte-identical R1CS and WASM. The
committed artifacts come from circom2 0.2.8. Version 0.2.23 does not reproduce
them byte for byte, so a compiler upgrade means a new reviewed artifact set.

`tooling/setup.sh` runs a new single-party test setup, not a production
ceremony, so whoever runs it could forge proofs. Run it only to replace the
test setup on purpose, then rebuild the activation manifest and proof
fixtures.

The native tests in [`devnet/native_occurrence/`](devnet/native_occurrence/README.md)
run real proofs through the pinned ethrex VM. They cover duplicate notes,
replay, rebuilding a proof after a reorg simulated by database rollback, settlement gas
and the fourth-frame rules, but not networking, fork choice, other clients or
FOCIL.

## What production would require

This repository is a research prototype and does not aim to become production
software. A pool meant to hold real value would need at least:

- A proving key built on a public multi-party phase 1 and an independently
  verified multi-party phase 2.
- Final versions of EIP-8141, EIP-8250 and EIP-8272 activated in a mainnet
  fork, and a pool built for exactly those versions.
- Published hashes of the final circuit, keys, verifier, dispatcher, logic and
  Poseidon contracts.
- Tests on other clients and under real network reorgs, the existing
  signature, capacity, reorg and gas tests rerun on the activation fork, and a
  proof that the settlement gas limits cover every settlement path under every
  supported gas schedule. The pool cannot be changed, so holders must exit
  before an unsupported repricing fork.
- A public mempool policy that admits the pool's validation budget and many
  pending spends from the pool at once.
- A nullifier domain that survives a chain ID change. `D` uses the chain ID
  at spend time, so on a chain that keeps the pool's state under a new ID, as
  the minority side of a contentious fork might, spent notes could be spent
  again.
- An independent audit of the contracts and the circuit.
- A way to deliver note details to recipients, since the pool publishes only
  commitments, and a real wallet that stores notes durably, handles reorgs and
  checks a pool's deployment before depositing.

See [SECURITY.md](SECURITY.md) for the trust model, privacy limits and known
risks.
