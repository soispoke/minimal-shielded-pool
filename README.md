# Minimal shielded pool

An immutable shielded pool for native ETH on the ethrex Hegotá testnet. It uses
EIP-8141 frame transactions, EIP-8250 keyed nonces and EIP-8272 recent roots.
It has no ERC-20 support, admin, governance or external paymaster.

This is research software. The committed Groth16 proving key comes from a
local test setup whose operator could have kept the toxic waste of either setup
phase, so the pool must never hold real value.

## How it works

A note commits to its owner, a random `rho` and its value:

```text
owner_pk = Poseidon3(1, spend_key, 0)
cm       = Poseidon3(2, Poseidon2(owner_pk, rho), value)
```

A spend proves a join-split with two inputs and two outputs. Its statement is
ten values: `[nf1, nf2, outCm1, outCm2, root, domain, publicAmount, fee,
recipient, authorizer]`. To save verification gas, the proof exposes three
public signals instead, using the hybrid compression of
[eprint 2025/1500](https://eprint.iacr.org/2025/1500): the pool computes
`alpha = keccak256(statement) mod p`, the circuit computes
`beta = Poseidon(statement)`, and both evaluate `gamma`, the statement as a
polynomial at `alpha + beta`. The ten values stay public in the settlement
data. The pool recomputes `alpha` and `gamma` from them and range-checks each
value itself, since the verifier no longer sees them. The circuit checks that
every positive input is in the tree, that value is conserved over 128-bit
amounts, and that at least one input carries value. It also requires distinct
nullifiers and outputs, a nonzero authorizer address, and a recipient exactly
when `publicAmount` is positive. A zero-value output must use a fixed "sink"
commitment for its position, which the pool never inserts.

Every deposit is a separate note, identified by its tree epoch and leaf index.
The nullifier binds that position, so two deposits of the same commitment are
spent independently and no uniqueness registry is needed:

```text
D  = keccak(domain_tag || chain_id || pool || epoch) mod r
nf = Poseidon3(4, Poseidon2(D, spend_key), Poseidon2(cm, leaf_index))
```

Here `domain_tag = keccak("minimal-shielded-pool:occurrence-domain:v1")` and
each field is 32 bytes. The epoch in `D` is the one the recent-root tuple names,
so a spend cannot combine notes from different epochs. Wallets must track notes
by position and rebuild positions after a reorg.

## Transactions

The pool is the sender and payer of every spend. The two nullifiers are the
transaction's EIP-8250 nonce keys at sequence zero, so the protocol rejects a
second spend of either note. A spend has three frames and an optional fourth:

1. `VERIFY(0x…8272, tuple)`: EIP-8272's recent-root check of the
   `(source_id, slot, root)` the proof uses. The slot comes from EIP-7843
   `slotNumber`.
2. `VERIFY(pool, proof)`: the pool checks the proof, binds it to that tuple,
   and checks the frame layout and the settlement frame's gas limits. It then
   approves execution and payment.
3. `SENDER(pool, settle(Spend))`: settlement inserts the outputs and records
   any withdrawal as a credit for `recipient`. It never publishes a root or
   calls the recipient, and the pool's `VERIFY` rejects anything settlement
   would refuse. Its gas limit must cover the worst tree shape, because running
   out after approval burns the notes.
4. Optional `DEFAULT` call: any nonzero target, including the pool, and any
   calldata, with zero value and flags. A withdrawal usually calls
   `claimWithdrawal(recipient)`. A transfer can call `publishEpochRoot` so the
   notes it creates can be spent from the next slot, though a spend against
   that root is then easy to link to the transfer. It must name the epoch its
   outputs land in, which is a new epoch if settlement starts a new tree.

The dispatcher pins the data length of the first three frames and the
settlement frame's gas limits. The validation frames' gas limits are wallet
defaults, except the recent-root frame's state limit, which EIP-8272 requires
to be zero. A limit that is too low only makes the transaction invalid, and
the proof's fee covers whatever is declared. Wallets can therefore raise these
limits after a gas repricing without a new pool, as long as the proof check
still fits the 500,000 gas the pool forwards to the verifier. Settlement's
limits are pinned, so a repricing that makes settlement more expensive needs a
new pool. Wallets should keep the defaults, since a spend with different limits
stands out.

| Frame | Execution gas | State gas | Data |
|---|---:|---:|---:|
| Recent root | 8,000 default (uses 5,579) | 0 pinned | 72 bytes |
| Proof | 225,000 default (uses about 210,000) | 195,840 default | 288 bytes |
| Settlement | 2,000,000 pinned | 550,000 pinned | 388 bytes |

The proof frame's data is the 256-byte proof followed by `beta`. It needs a
limit of about 216,000, although it uses about 210,000, because each nested
call keeps back 1/64 of its gas (EIP-150). Below
that, the verifier runs out of gas and the pool reports an invalid proof. The
proof frame's state gas pays for creating the two nullifier keys.

The proof names a secp256k1 authorizer, which the wallet makes fresh for each
spend. Its signature covers the
whole transaction, including the proof, the recent-root tuple and the fourth
frame. The proof's `fee` must cover the transaction's maximum cost; any unused
part stays in the pool.

The wallet chooses the fourth frame's limits. Intrinsic gas plus every frame's
execution limit, or the calldata floor when larger, must fit EIP-7825's `2^24`
cap, of which the pool's own frames use 2.23M by default; state gas is
budgeted separately. The encoded transaction must also fit ethrex's 128 KiB
mempool limit.

If the fourth frame fails or is left out, settlement still stands, and a
withdrawal remains as a credit that anyone can pay out later with
`claimWithdrawal(recipient)`. A failed fourth frame makes the receipt's overall
status 0 even though settlement succeeded, so check each frame's status. The
claim pays `recipient` with a plain ETH transfer and cannot redirect it, so the
recipient must accept one.

A called account sees EIP-8141's entry point as its caller, so it must
authenticate its own owner. This is a direct account call, not an ERC-4337
adapter. See [SECURITY.md](SECURITY.md#generic-default-tail).

When the current tree lacks room for the notes being inserted, the pool starts
a new epoch first, for shields and settlements alike. Sinks take no space, so a
note can always be withdrawn. Anyone may publish the pool's current or final
epoch root to EIP-8272.

## Code

```
circuits/spend.circom
contracts/src/Groth16Verifier.sol
contracts/src/ShieldedPoolLogic.sol
contracts/src/PoseidonT3.sol
contracts/src/PoseidonT4.sol
devnet/ShieldedPoolDispatcher.yul
devnet/dispatcher.py
devnet/pool_frametx.py
wallet/wallet.py
wallet/gen_smoke.py
```

## Deployment

This is pool profile `position-notes-v2`. It follows current EIP-8141,
EIP-8250 at `f3079a09e8` and EIP-8272 at `824cbc0b0e`: an eight-field envelope
with separate execution and state gas limits for each frame. Because the EIPs
are drafts, each supported combination is a separate profile, and profiles are
not wire compatible. The previous chain-8141 dialect is archived byte for byte
under `devnet/vectors/2026-09-01-hegota-final-profile/`.

Each profile needs its own deployment. Replacing the verifier under an old pool
could make spent notes spendable again, and a `position-notes-v1` pool rejects
this profile's validation limits. `devnet/deploy_config.json` still records the
`position-notes-v1` deployment on chain 8141 (pool `0xac01…b100`, commit
`c26b8e4`), which completed shield, transfer, withdrawal and fourth-frame calls
on September 22, 2026. The CLI refuses to shield into or spend from that pool.

Before shielding or spending, the CLI requires the config to name this profile
and checks the pool itself: the RPC must be on the configured chain, the pool's
code must be exactly what this profile's dispatcher deploys when linked to the
logic and verifier the config records, and its `domain(uint64)` must match the
profile's formula. The code check matters because both profiles share the
domain formula. The linked verifier must also accept a reference proof and
reject it with `gamma` changed. These checks catch a stale or mislabeled config,
not a malicious deployer: they trust the config's logic and verifier, which the
deployment script verified, and cannot see what a pool's constructor wrote to
storage. Before depositing into a pool someone else deployed, check its
deployment transactions.

A shield also refuses a fixture made for another chain, pool or epoch, or one
whose note would not land at the leaf and on the tree its proofs expect.
Before sending, and with `--dry-run`, the CLI gives the RPC the fully signed
transaction for simulation, and the RPC could broadcast it. Use an RPC you
trust.

The public mempool counts the two validation frames' declared limits plus
2,800 gas for the signature: 235,800 by default, while a spend uses about
218,500. That is well above EIP-8141's published default of 100,000. The chain
8141 testnet admits it; other networks need a policy that does.
[EIP-8369](https://eips.ethereum.org/EIPS/eip-8369) has not settled a
per-transaction budget.

## Test

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
committed artifacts come from circom2 0.2.8; 0.2.23 does not reproduce them
byte for byte, so a compiler upgrade means a new reviewed artifact set. Run `tooling/setup.sh`
only to replace the test setup on purpose, then rebuild the activation manifest
and proof fixtures.

The native tests in [`devnet/native_occurrence/`](devnet/native_occurrence/README.md)
run real proofs through the pinned ethrex VM. They cover duplicate notes,
replay, reorgs, settlement gas and the fourth-frame rules, but not networking,
other clients or FOCIL.

## Before real value

- Replace the test proving key with one built on a public multi-party phase 1
  and an independently verified multi-party phase 2.
- Publish the hashes of the final circuit, keys, verifier, dispatcher, logic
  and Poseidon contracts.
- Rerun the signature, capacity, reorg, gas and cross-client tests on the
  activation fork. Recheck the settlement gas limits under every supported gas
  schedule. The pool cannot be changed, so holders must exit before an
  unsupported repricing fork.
- Obtain an independent contract and circuit audit.

See [SECURITY.md](SECURITY.md) for trust and failure boundaries.
