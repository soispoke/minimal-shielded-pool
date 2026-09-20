# Native withdrawal and swap tests

This suite executes complete signed transactions on ethrex's native Hegota
VM at `247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e`. It deploys the real pool,
verifier and Poseidon contracts, shields notes, publishes a root, and executes
real Groth16 proofs. The recipient account reads native frame opcodes and
checks its own EIP-712 signature.

All 24 scenarios pass, including 491 signed transaction executions with setup
repeated from a fresh state for each scenario. The ETH-to-DAI example uses
the official Uniswap V2 factory, pair, router and WETH contracts, plus a local
DAI test token. A market funded with 100 ETH and 200,000 test DAI swaps a
0.95 ETH withdrawal for about 1,876.52647945 test DAI.

| Fourth frame | Execution gas | Net state gas | Declared limits |
|---|---:|---:|---|
| Claim to a new EOA | 14,716 | 183,600 | 100,000 / 183,600 |
| Claim and swap | 210,779 | 391,680 | 300,000 / 500,000 |

The swap needs **489,600 state gas at its peak**, before the account's reentry
guard is cleared. It succeeds at that limit and fails at 489,599. The receipt's
391,680 net charge therefore must not be used as the frame's budget. The test
advances time after liquidity setup, so the first swap also creates both
cumulative-price slots in the pair.

## Run

Use Rust with edition 2024 support and the dependencies in `Cargo.lock`. The
recorded run used rustc 1.97.1 and Cargo 1.96.0.

```sh
python3 devnet/native_recipient_pull/run.py
```

The runner downloads and verifies the pinned client source, checks that the
pool sources still match these fixtures, and builds outside this repository.
It does not alter client behavior. To reuse a local client checkout or an
existing dependency cache:

```sh
ETHREX_SOURCE=/path/to/ethrex \
NATIVE_WORKDIR=/tmp/pool-native-tests \
python3 devnet/native_recipient_pull/run.py --offline
```

`ETHREX_SOURCE` must match the recorded source hashes. `--offline` applies to
Cargo; provide the client source or cached archive as well. `CARGO_BIN` can
select a Cargo executable. `NATIVE_REPORT` selects the full JSON report path.
The concise recorded results are in [results.json](results.json).

## What is checked

Transfers retain three frames. Ordinary withdrawals claim in the fourth.
The swap checks the exact token output, spent note keys, account nonce, pool
credit and fee-adjusted balances. Reusing the signed spend fails with a nonce
mismatch.

Slippage failure, bad account authorization, a request for another settlement,
and exhaustion of either gas dimension preserve the settled credit. The suite
compares all account state before and after each failed tail: only the pool,
nonce manager and fee recipient may change. A separate signed recovery
transaction must deliver the entire credit to the owner, less its own gas.

A deliberately conflicting output makes settlement fail. The account then
rejects the action even when it holds credit from an earlier withdrawal.
This reproduces an existing production blocker: a recipient who knows a
positive output's opening can pre-shield that commitment after the sender
signs. The proof still passes, approval consumes the input nonce keys, and
settlement rejects the duplicate without creating the promised outputs. The
fourth frame behaves correctly after that failure, but it cannot repair it.
Invalid proof, signature, recent-root, frame count, recipient, mode, flags,
value and gas bounds reject before any persistent state changes. An explicit
call to a code-less recipient can succeed without claiming; that case confirms
why a wallet must select a compatible account.

This exercises real native transaction execution and both gas dimensions.
It does not test gossip, mempool admission, block import, a persisted state
root, or another client's implementation. The recent-root code is the pinned
ethrex implementation of the draft EIP. The account and DAI token are test
fixtures, and the balances and keys have no real value. Gas measurements apply
to this account and swap path; other accounts and actions need their own tests.

## Regenerate fixtures

The signed raw transactions include deployment bytecode and real proofs, so
running the suite needs no Solidity or proving toolchain. To regenerate them:

```sh
npm ci --prefix tooling
npm ci --prefix devnet/native_recipient_pull/dex --ignore-scripts
forge build --root contracts
FOUNDRY_PROFILE=libsmall forge build --root contracts
python3 devnet/native_recipient_pull/scripts/compile_contracts.py
python3 devnet/native_recipient_pull/scripts/generate_fixtures.py
```

The generator uses the committed disposable proving key and verifies each
new proof off-chain. Review changed bytecode and proofs before refreshing
`pool-source-hashes.json`; do not update hashes merely to silence a mismatch.
The package lock pins Uniswap core 1.0.1 and periphery 1.1.0-beta.0. Their
factory and router use the same pair creation-code hash.

The Uniswap artifacts retain their upstream licenses, copied in `dex/`.
Their corresponding source is included in the pinned npm packages.
