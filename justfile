# Run `just` to list the recipes. CI runs the same commands
# (.github/workflows/ci.yml), plus a dependency audit and a check of the
# archived profile under evidence/.

default:
    @just --list

# Install the pinned npm toolchain and the Python dependencies.
install:
    npm ci --prefix tools
    python3 -m pip install --requirement requirements.txt

# What CI's test job runs, in the same order.
test: check-artifacts test-python test-contracts

# Rebuild the circuit and the dispatcher, and fail if either differs from core/artifacts.
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

# The Python tests and the activation, gas and compiler-settings checks.
test-python:
    python3 -m py_compile tools/dispatcher.py sdk/frametx.py sdk/gas_profile.py sdk/pool_frametx.py test/test_pool_envelope_binding.py test/test_gas_only_action.py test/test_recent_root_window.py test/test_occurrence_profile.py test/test_deploy_checks.py test/test_occurrence.py test/test_wallet_occurrence.py test/test_generators.py sdk/disclosure.py test/test_disclosure.py sdk/notes.py test/test_notes.py sdk/gen_nonce_race.py sdk/gen_smoke.py sdk/wallet.py tools/gen_poseidon_sol.py sdk/poseidon_bn254.py tools/check_activation.py tools/check_forge_config.py tools/check_gas_profile.py tools/check_formal_pins.py test/test_check_activation.py tools/patch_verifier.py
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

# Format, lint and test the contracts.
test-contracts:
    forge fmt --root core/contracts --check
    forge lint --root core/contracts --deny warnings
    forge test --root core/contracts --force -vv

# Deploy a fresh testbed pool, then shield, transfer and withdraw through it. The
# script lists the variables it needs (RPC_URL, a Foundry keystore and its
# password file, ALLOW_TESTBED_SETUP=1) and rewrites core/deploy_config.json.
deploy:
    tools/run_live_dispatcher.sh

# Regenerate the Poseidon contracts from sdk/poseidon_bn254_constants.json. The
# pinned files match only after forge fmt.
poseidon:
    python3 tools/gen_poseidon_sol.py
    python3 tools/split_poseidon.py
    cd core/contracts && forge fmt src/PoseidonBN254.sol src/PoseidonT3.sol src/PoseidonT4.sol

# The native suite: real proofs through the pinned ethrex VM (see test/native/README.md).
# The ethrex path may be relative to the directory you run just from.
native ethrex_source:
    python3 test/native/run.py --ethrex-source "{{join(invocation_directory(), ethrex_source)}}"

# Report which formally verified files differ from the verified commit.
formal-pins:
    python3 tools/check_formal_pins.py
