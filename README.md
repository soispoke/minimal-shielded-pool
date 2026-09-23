# Minimal shielded pool

An immutable shielded pool for native ETH on the ethrex Hegotá testnet. It uses
EIP-8141 frame transactions, EIP-8250 keyed nonces and EIP-8272 recent roots.
It has no ERC-20 support, admin, governance or external paymaster.

This is research software. The committed Groth16 proving key comes from a
single test-only setup whose operator could have kept the toxic waste, so the
pool must never hold real value.

## How it works

A note commits to its owner, a random `rho` and its value:

```text
owner_pk = Poseidon3(1, spend_key, 0)
cm       = Poseidon3(2, Poseidon2(owner_pk, rho), value)
```

A spend proves a join-split with two inputs and two outputs. Its ten public
signals are `[nf1, nf2, outCm1, outCm2, root, domain, publicAmount, fee,
recipient, authorizer]`. The circuit checks that every positive input is in the
tree, that value is conserved over 128-bit amounts, and that at least one input
carries value. It also requires distinct nullifiers and outputs, a nonzero
authorizer address, and a recipient exactly when `publicAmount` is positive. A
zero-value output must use a fixed "sink" commitment for its position, which
the pool never inserts.

Every deposit is a separate note, identified by its tree epoch and leaf index.
The nullifier binds that position, so two deposits of the same commitment are
spent independently and no uniqueness registry is needed:

```text
D  = keccak(domain_tag || chain_id || pool || epoch) mod r
nf = Poseidon3(4, Poseidon2(D, spend_key), Poseidon2(cm, leaf_index))
```

Here `domain_tag = keccak("minimal-shielded-pool:occurrence-domain:v1")` and
each field is 32 bytes. Wallets must track notes by position and rebuild
positions after a reorg.

## Transactions

The pool is the sender and payer of every spend. The two nullifiers are the
transaction's EIP-8250 nonce keys at sequence zero, so the protocol rejects a
second spend of either note. A spend has three frames and an optional fourth:

1. `VERIFY(0x…8272, tuple)`: EIP-8272's recent-root check of the
   `(source_id, slot, root)` the proof uses. The slot comes from EIP-7843
   `slotNumber`.
2. `VERIFY(pool, proof)`: the pool checks the proof, binds it to that tuple,
   and checks the frame layout and pinned gas limits. It then approves
   execution and payment.
3. `SENDER(pool, settle(Spend))`: settlement inserts the outputs and records
   any withdrawal as a credit for `recipient`. It never publishes a root or
   calls the recipient, and the pool's `VERIFY` rejects anything settlement
   would refuse.
4. Optional `DEFAULT` call: any nonzero target and calldata, with zero value
   and flags. Only a withdrawal may target the pool; its usual call is
   `claimWithdrawal(recipient)`.

The proof names a fresh secp256k1 authorizer, and its signature covers the
whole transaction, including the proof, the recent-root tuple and the fourth
frame. The proof's `fee` must cover the transaction's maximum cost; any unused
part stays in the pool.

The fourth frame is chosen by the wallet. Its gas must fit within EIP-7825's
`2^24` transaction limit, and the whole transaction within ethrex's 128 KiB
mempool limit. If the call fails or is left out, settlement still stands and a
withdrawal remains as a credit that anyone can pay out later with
`claimWithdrawal(recipient)`. A called account sees EIP-8141's entry point as
its caller, so it must authenticate its own owner. This is a direct account
call, not an ERC-4337 adapter. See [SECURITY.md](SECURITY.md#generic-default-tail).

When the tree is full, settlement starts a new epoch before inserting outputs.
Sinks take no space, so a note can always be withdrawn. Anyone may publish the
pool's current or final epoch root to EIP-8272.

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

This is pool profile `position-notes-v1`. It follows current EIP-8141,
EIP-8250 at `f3079a09e8` and EIP-8272 at `824cbc0b0e`: an eight-field envelope
with separate execution and state gas limits for each frame. Because the EIPs
are drafts, each supported combination is a separate profile, and profiles are
not wire compatible. The previous chain-8141 dialect is archived byte for byte
under `devnet/vectors/2026-09-01-hegota-final-profile/`.

The profile needs its own deployment, since its nullifiers and storage differ
from earlier pools. Replacing the verifier under an old pool could make spent
notes spendable again. `devnet/deploy_config.json` records the deployment on
chain 8141 (pool `0xac01…b100`, commit `c26b8e4`), which completed shield,
transfer, withdrawal and fourth-frame calls on September 22, 2026. Before
shielding or spending, the CLI checks that the RPC is on the configured chain
and that the pool's `domain(uint64)` matches this profile.

Validation needs 352,800 execution gas, well above EIP-8141's published
100,000 public-mempool default. The chain 8141 testnet admits it; other
networks need a policy that does. [EIP-8369](https://github.com/ethereum/EIPs/pull/12110)
has not settled a per-transaction budget.

## Test

```sh
npm ci --prefix tooling
python3 -m pip install --requirement requirements.txt

python3 devnet/frametx.py
python3 devnet/test_pool_envelope_binding.py
python3 devnet/test_gas_only_action.py
python3 devnet/test_recent_root_window.py
python3 devnet/test_occurrence_profile.py
python3 wallet/test_occurrence.py
python3 wallet/test_wallet_occurrence.py
python3 tooling/check_gas_profile.py
python3 tooling/check_activation.py activation_manifest.testbed.json --allow-testbed
python3 tooling/test_check_activation.py
python3 wallet/wallet.py
python3 reference/poseidon_bn254.py

forge fmt --root contracts --check
forge lint --root contracts --deny warnings
forge test --root contracts --force -vv
```

CI also rebuilds the circuit and requires byte-identical R1CS and WASM. The
tools are pinned to the committed artifacts; a newer circom2 does not reproduce
them, so upgrading it means a new reviewed artifact set. Run `tooling/setup.sh`
only to replace the test setup on purpose, then rebuild the activation manifest
and proof fixtures.

The native tests in [`devnet/native_occurrence/`](devnet/native_occurrence/README.md)
run real proofs through the pinned ethrex VM. They cover duplicate notes,
replay, reorgs, settlement gas and the fourth-frame rules, but not networking,
other clients or FOCIL.

## Before real value

- Replace the test proving key with an independently verified multi-party
  ceremony.
- Publish the hashes of the final circuit, keys, verifier, dispatcher, logic
  and Poseidon contracts.
- Rerun the signature, capacity, reorg, gas and cross-client tests on the
  activation fork. Recheck the settlement gas limits under every supported gas
  schedule, and deactivate the profile before an unsupported repricing fork.
- Obtain an independent contract and circuit audit.

See [SECURITY.md](SECURITY.md) for trust and failure boundaries.
