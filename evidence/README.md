# Evidence

Dated records of devnet runs, reviews and deployments. Each describes the
repository as it was when it was written, so paths inside them use the old
layout:

- `circuits/` and `contracts/` are now `core/circuits/` and `core/contracts/`;
- `build/`, `devnet/build/` and `contracts/vectors/` are now `core/artifacts/`;
- `activation_manifest.testbed.json` and `devnet/deploy_config.json` are now
  in `core/`, and `devnet/ShieldedPoolDispatcher.yul` is in `core/dispatcher/`;
- the Python client from `wallet/`, `reference/` and `devnet/` is in `sdk/`,
  its tests and fixtures are in `test/`, and `devnet/native_occurrence/` is
  `test/native/`;
- `tooling/` and the remaining scripts are in `tools/`;
- `devnet/REVIEW.md` and `devnet/LATEST-CONFORMANCE-TESTS.md` are now in this
  directory;
- `devnet/vectors/` is `vectors/` here.

A few comments in formally pinned files under `core/` also keep old paths,
since editing them would change what the proofs pin.

`vectors/2026-09-01-hegota-final-profile/` is the byte-exact archive of the
format chain 8141 used before its relaunch. CI checks it against commit
`6c5c77b`.
