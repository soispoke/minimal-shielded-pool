#!/usr/bin/env python3
"""The new proof format must not be submitted to the recorded old deployment."""
import contextlib
import io
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest import mock

import pool_frametx as builder
from gas_profile import POOL_PROFILE

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "wallet"))
import wallet as w  # noqa: E402


def check_profile_labels():
    original = json.loads((ROOT / "devnet/deploy_config.json").read_text())
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "config.json"
        for profile in ("recipient-pull-v1", "eip8272-canonical-frame", None):
            cfg = dict(original, profile=profile)
            path.write_text(json.dumps(cfg))
            for operation in ("transfer", "withdraw"):
                result = subprocess.run([
                    sys.executable, str(ROOT / "devnet/pool_frametx.py"),
                    "http://127.0.0.1:1", str(path), str(ROOT / "wallet/smoke_fixture.json"),
                    operation, "01" * 32, "--dry-run",
                ], capture_output=True, text=True)
                assert result.returncode != 0, (profile, operation)
                assert f"spends require profile={POOL_PROFILE}" in result.stderr, result.stderr


def check_recorded_deployment():
    cfg = json.loads((ROOT / "devnet/deploy_config.json").read_text())
    assert cfg["profile"] == POOL_PROFILE
    pool = int(cfg["pool"], 16)
    domain = builder.expected_domain(cfg["chainId"], pool)
    assert domain == int(cfg["domain"], 16), "recorded domain is not this profile's formula"
    assert domain == w.domain_scalar(cfg["chainId"], cfg["pool"], 0)
    source = builder._keccak(pool.to_bytes(20, "big") + bytes(32))
    assert source.hex() == cfg["sourceIdEpoch0"].removeprefix("0x")


def check_deployed_domain_gate():
    """The gate reads the deployed pool, so a relabeled old pool is refused."""
    chain_id, pool = 8141, 0xAC01C30F28B32DD31D3C2854012E673E74F6B100
    good = "0x" + builder.expected_domain(chain_id, pool).to_bytes(32, "big").hex()
    wrong = "0x" + builder.expected_domain(chain_id, pool, 1).to_bytes(32, "big").hex()
    real_rpc = builder.rpc

    def fake(call_result):
        def rpc(url, method, params):
            if method == "eth_chainId":
                return hex(chain_id)
            assert method == "eth_call"
            assert params[0]["data"] == "0x" + (builder._keccak(b"domain(uint64)")[:4] + bytes(32)).hex()
            if isinstance(call_result, Exception):
                raise call_result
            return call_result
        return rpc

    cases = {
        "pre-position-notes pool reverts on domain(uint64)": RuntimeError("execution reverted"),
        "address without code": "0x",
        "domain from another epoch": wrong,
    }
    try:
        for label, result in cases.items():
            builder.rpc = fake(result)
            try:
                builder.check_deployed_profile("http://node", pool)
            except SystemExit as error:
                assert POOL_PROFILE in str(error), (label, error)
            else:
                raise AssertionError(f"accepted {label}")
        builder.rpc = fake(good)
        builder.check_deployed_profile("http://node", pool)
        builder.check_deployed_profile("http://node", pool, chain_id)
        # A genuine pool at the same address on the RPC's chain is still refused
        # when the config names another chain.
        try:
            builder.check_deployed_profile("http://node", pool, 1)
        except SystemExit as error:
            assert "config names chain 1" in str(error), error
        else:
            raise AssertionError("accepted an RPC on a different chain")
    finally:
        builder.rpc = real_rpc


def check_cli_runs_deployed_gate():
    """shield, transfer and withdraw check the deployed pool before anything else."""
    cfg_path = ROOT / "devnet/deploy_config.json"
    chain_id = json.loads(cfg_path.read_text())["chainId"]

    def rpc(url, method, params):
        if method == "eth_chainId":
            return hex(chain_id)
        if method == "eth_call":
            return "0x"
        raise AssertionError(f"{method} called before the deployed-pool check")

    for operation in ("shield", "transfer", "withdraw"):
        argv = ["pool_frametx.py", "http://node", str(cfg_path),
                str(ROOT / "wallet/smoke_fixture.json"), operation, "01" * 32]
        with mock.patch.object(builder, "rpc", rpc), mock.patch.object(sys, "argv", argv), \
                contextlib.redirect_stdout(io.StringIO()):
            try:
                builder.main()
            except SystemExit as error:
                assert "does not expose domain(uint64)" in str(error), (operation, error)
            else:
                raise AssertionError(f"{operation} ran without the deployed-pool check")


def main():
    assert POOL_PROFILE == "position-notes-v1"
    check_profile_labels()
    check_recorded_deployment()
    check_deployed_domain_gate()
    check_cli_runs_deployed_gate()
    print("PASS: six incompatible profile labels rejected before RPC; recorded deployment "
          "matches this profile; relabeled, codeless, wrong-domain and wrong-chain pools refused; "
          "shield, transfer and withdraw run the check")


if __name__ == "__main__":
    main()
