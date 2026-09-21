# Native gas-only account-action evidence

This fixture exercises the optional fourth `DEFAULT` account frame against the
pinned ethrex Hegota native VM. It uses real Groth16 proofs and the repository's
compiled dispatcher. The existing test account starts with test tokens and no
ETH; the pool pays FrameTx gas while the account independently authenticates
its owner and the successful pool settlement.

The account and token are test fixtures, not production wallet code. The run is
finite native-VM evidence only. It does not test networking, block import,
mempool replacement, another client, or compatibility with arbitrary deployed
smart accounts.

All 23 scenarios passed on ethrex
`247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e`. Coverage includes a token action
from a zero-ETH account, private-change preservation after action failure,
settlement-context rejection, and a stale account nonce in a separately signed
new spend. The old-signature target mutation uses an EOA, so an omitted account
signature check would let the call succeed.

The runner verifies hashes of the relevant client source files before it runs.
From the repository root:

```sh
python3 devnet/native_gas_actions/run.py \
  --ethrex-source /path/to/ethrex-247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e
```

Use `--skip-generate` to execute the committed raw vectors without rebuilding
Solidity or proofs. `--offline` is available when the Cargo registry is already
cached. The generated compact report is `native-report.json`.
