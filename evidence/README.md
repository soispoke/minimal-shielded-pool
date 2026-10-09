# Evidence

Dated records of devnet runs, reviews and deployments. Each describes the
repository as it was when it was written, so paths inside them use the old
layout:

- `circuits/` and `contracts/` are now `core/circuits/` and `core/contracts/`;
- `build/`, `devnet/build/` and `contracts/vectors/` are now `core/artifacts/`;
- `activation_manifest.testbed.json` and `devnet/deploy_config.json` are now
  in `core/`, and `devnet/ShieldedPoolDispatcher.yul` is in `core/dispatcher/`;
- the Python client from `wallet/`, `reference/` and `devnet/`, later in
  `sdk/`, is now the TypeScript client in `src/`; the tests and fixtures are
  in `test/`, and `devnet/native_occurrence/` is `test/native/`;
- the scripts from `tooling/` and the remaining scripts are in `tools/`, and
  `tooling/`'s npm packages are pinned in the root `package.json`;
- `devnet/REVIEW.md` and `devnet/LATEST-CONFORMANCE-TESTS.md` are now in this
  directory;
- `devnet/vectors/` is `vectors/` here.

Apart from the frozen copies in the archive below, each Python module became
the TypeScript file with the same role, usually under its own name in kebab
case: `frametx.py` is `src/frametx.ts`, `dispatcher.py` is
`tools/dispatcher.ts` and `check_activation.py` is `tools/check-activation.ts`.
A few took new names: `pool_frametx.py` is `src/pool.ts`, `poseidon_bn254.py`
is `src/poseidon.ts`, `gen_smoke.py` and `gen_nonce_race.py` are
`src/smoke.ts` and `src/nonce-race.ts` (each with a command in `src/cli/`), and
`gen_poseidon_sol.py` and `split_poseidon.py` are together
`tools/poseidon-sol.ts`. Modules removed before the port, such as `yul_pool.py`
and `paymaster.py`, are only in git history.

A few comments in formally pinned files under `core/` also keep old paths,
since editing them would change what the proofs pin.

`vectors/2026-09-01-hegota-final-profile/` is the byte-exact archive of the
format chain 8141 used before its relaunch. CI checks it against commit
`6c5c77b`.
