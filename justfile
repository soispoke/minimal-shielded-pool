# Run `just` to list the recipes. CI's test job runs install, check-artifacts,
# test-python and test-contracts, plus a dependency audit
# (.github/workflows/ci.yml).

default:
    @just --list

# Install the pinned npm toolchain and the Python dependencies.
install:
    npm ci --prefix tools
    python3 -m pip install --requirement requirements.txt

# What CI's test job runs, in the same order.
test: check-artifacts test-python test-contracts

# The archive check compares with commit 6c5c77b, so it needs the full git
# history.
# Rebuild the circuit and dispatcher, and check them and the archived profile.
check-artifacts:
    #!/usr/bin/env bash
    set -euo pipefail
    out=$(mktemp -d)
    tools/node_modules/.bin/circom2 core/circuits/spend.circom --r1cs --wasm --sym -l tools/node_modules -o "$out"
    tools/node_modules/.bin/snarkjs r1cs info "$out/spend.r1cs"
    cmp "$out/spend.r1cs" core/artifacts/spend.r1cs
    cmp "$out/spend_js/spend.wasm" core/artifacts/spend_js/spend.wasm
    forge build --root core/contracts
    python3 tools/dispatcher.py --artifact >/dev/null
    git diff --exit-code -- core/artifacts/shielded_pool_dispatcher_init.hex
    python3 tools/dispatcher.py --initcode 0x0000000000000000000000000000000000000001 0x0000000000000000000000000000000000000002 >/dev/null
    git diff --exit-code 6c5c77b171e08ad0987a06c44d0488ab385f36dd:devnet/vectors/2026-09-01-hegota-final-profile HEAD:evidence/vectors/2026-09-01-hegota-final-profile
    git diff --exit-code HEAD -- evidence/vectors/2026-09-01-hegota-final-profile

# The Python tests and the activation, gas and compiler-settings checks.
test-python:
    python3 -m compileall -q -x node_modules sdk tools test
    python3 sdk/frametx.py
    python3 test/test_pool_envelope_binding.py
    python3 test/test_gas_only_action.py
    python3 test/test_recent_root_window.py
    python3 test/test_occurrence_profile.py
    python3 test/test_deploy_checks.py
    python3 test/test_occurrence.py
    python3 test/test_wallet_occurrence.py
    python3 test/test_generators.py
    python3 test/test_disclosure.py
    python3 test/test_notes.py
    python3 tools/check_gas_profile.py
    python3 tools/check_activation.py core/activation_manifest.testbed.json --allow-testbed
    python3 tools/check_forge_config.py core/activation_manifest.testbed.json core/contracts
    python3 test/test_check_activation.py
    python3 sdk/wallet.py
    python3 sdk/poseidon_bn254.py

# --force recompiles, so a cache left by an earlier build cannot shrink the suite.
# Format, lint and test the contracts.
test-contracts:
    forge fmt --root core/contracts --check
    forge lint --root core/contracts --deny warnings
    forge test --root core/contracts --force -vv

# The script lists the variables it needs (RPC_URL, a Foundry keystore and its
# password file, ALLOW_TESTBED_SETUP=1) and rewrites core/deploy_config.json.
# Deploy a fresh testbed pool, then shield, transfer and withdraw through it.
deploy:
    tools/run_live_dispatcher.sh

# The pinned files match only after the last step, forge fmt.
# Regenerate the Poseidon contracts from sdk/poseidon_bn254_constants.json.
poseidon:
    python3 tools/gen_poseidon_sol.py
    python3 tools/split_poseidon.py
    cd core/contracts && forge fmt src/PoseidonBN254.sol src/PoseidonT3.sol src/PoseidonT4.sol

# The ethrex path may be relative to the directory you run just from.
# Run real proofs through the pinned ethrex VM (see test/native/README.md).
native ethrex_source:
    python3 test/native/run.py --ethrex-source "{{join(invocation_directory(), ethrex_source)}}"

# Report which formally verified files differ from the verified commit.
formal-pins:
    python3 tools/check_formal_pins.py
