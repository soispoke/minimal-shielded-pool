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
from gas_profile import POOL_PROFILE, PREVIOUS_POOL_PROFILE

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "wallet"))
import wallet as w  # noqa: E402


ABSENT = object()


def check_profile_labels():
    """Every operation refuses a config for another profile, or without one, before RPC."""
    original = json.loads((ROOT / "devnet/deploy_config.json").read_text())
    runs = 0
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "config.json"
        for profile in (PREVIOUS_POOL_PROFILE, "recipient-pull-v1", "eip8272-canonical-frame",
                        None, ABSENT):
            cfg = dict(original, profile=profile)
            if profile is ABSENT:
                del cfg["profile"]
            path.write_text(json.dumps(cfg))
            for operation in ("shield", "transfer", "withdraw"):
                result = subprocess.run([
                    sys.executable, str(ROOT / "devnet/pool_frametx.py"),
                    "http://127.0.0.1:1", str(path), str(ROOT / "wallet/smoke_fixture.json"),
                    operation, "01" * 32, "--dry-run",
                ], capture_output=True, text=True)
                assert result.returncode != 0, (profile, operation)
                assert f"{operation} requires profile={POOL_PROFILE}" in result.stderr, result.stderr
                runs += 1
    return runs


def check_recorded_deployment():
    cfg = json.loads((ROOT / "devnet/deploy_config.json").read_text())
    # Until this profile is deployed the record names the previous one, which the
    # spend CLI refuses. Both profiles share the domain formula checked here.
    assert cfg["profile"] in (POOL_PROFILE, PREVIOUS_POOL_PROFILE)
    pool = int(cfg["pool"], 16)
    domain = builder.expected_domain(cfg["chainId"], pool)
    assert domain == int(cfg["domain"], 16), "recorded domain is not this profile's formula"
    assert domain == w.domain_scalar(cfg["chainId"], cfg["pool"], 0)
    source = builder._keccak(pool.to_bytes(20, "big") + bytes(32))
    assert source.hex() == cfg["sourceIdEpoch0"].removeprefix("0x")


DOMAIN_CALL = "0x" + (builder._keccak(b"domain(uint64)")[:4] + bytes(32)).hex()


def deployed(initcode):
    """Stand-in for a node's simulated deployment: different initcode, different code."""
    return "0x" + builder._keccak(bytes.fromhex(initcode.removeprefix("0x"))).hex()


def linked(initcode, logic, verifier):
    return initcode + f"{logic:064x}{verifier:064x}"


def word(value):
    return "0x" + value.to_bytes(32, "big").hex()


def fake_node(chain_id, pool_code, domain, verifier="committed"):
    """A node holding the pool's code and, at the linked verifier address, a
    verifier that behaves as named: the committed one, one with the previous
    ten-input interface (reverts), one for another proving key (rejects all), or
    one that accepts any proof."""
    good, _ = builder.reference_verifier_calls()

    def rpc(url, method, params):
        if method == "eth_chainId":
            return hex(chain_id)
        if method == "eth_getCode":
            return pool_code
        if method == "eth_call" and "to" not in params[0]:
            if isinstance(pool_code, Exception):
                raise pool_code
            return deployed(params[0]["data"])
        if method == "eth_call" and params[0]["data"].startswith("0x11479fea"):
            if verifier == "previous-interface":
                raise RuntimeError("execution reverted")
            if verifier == "other-key":
                return word(0)
            if verifier == "accepts-any":
                return word(1)
            return word(1 if params[0]["data"] == good else 0)
        if method == "eth_call" and params[0]["data"] == DOMAIN_CALL:
            if isinstance(domain, Exception):
                raise domain
            return domain
        raise AssertionError(f"{method} called before the deployed-pool check finished")
    return rpc


def recorded_pool():
    """The recorded chain 8141 pool, and the stand-in code of the previous profile's
    dispatcher there: same logic, verifier and domain, different dispatcher code."""
    cfg = json.loads((ROOT / "devnet/deploy_config.json").read_text())
    initcode = (ROOT / "devnet/build/shielded_pool_dispatcher_init.hex").read_text().strip()
    logic, verifier = int(cfg["logic"], 16), int(cfg["verifier"], 16)
    previous = initcode[:-2] + f"{int(initcode[-2:], 16) ^ 1:02x}"
    return cfg, initcode, logic, verifier, deployed(linked(previous, logic, verifier))


def check_deployed_pool_gate():
    """The gate compares the deployed code, so the previous profile's pool is refused
    although its domain matches."""
    cfg, initcode, logic, verifier, previous_code = recorded_pool()
    chain_id, pool = cfg["chainId"], int(cfg["pool"], 16)
    this_code = deployed(linked(initcode, logic, verifier))
    good = "0x" + builder.expected_domain(chain_id, pool).to_bytes(32, "big").hex()
    wrong = "0x" + builder.expected_domain(chain_id, pool, 1).to_bytes(32, "big").hex()
    not_dispatcher = f"is not the {POOL_PROFILE} dispatcher"
    not_verifier = f"does not verify {POOL_PROFILE} proofs"
    cases = {
        "previous profile's dispatcher with a matching domain": (previous_code, good, not_dispatcher),
        "this dispatcher linked to other logic": (
            deployed(linked(initcode, logic ^ 1, verifier)), good, not_dispatcher),
        "this dispatcher linked to another verifier": (
            deployed(linked(initcode, logic, verifier ^ 1)), good, not_dispatcher),
        "address without code": ("0x", good, not_dispatcher),
        "node cannot simulate a deployment": (
            RuntimeError("unsupported"), good, "could not simulate"),
        "pool reverts on domain(uint64)": (
            this_code, RuntimeError("execution reverted"), "does not expose domain(uint64)"),
        "domain from another epoch": (this_code, wrong, "domain(0) does not match"),
        "this dispatcher linked to the previous ten-input verifier": (
            this_code, good, not_verifier, "previous-interface"),
        "this dispatcher linked to a verifier for another proving key": (
            this_code, good, not_verifier, "other-key"),
        "this dispatcher linked to a verifier that accepts any proof": (
            this_code, good, not_verifier, "accepts-any"),
    }
    real_rpc = builder.rpc
    try:
        for label, (code, domain, expected, *behavior) in cases.items():
            builder.rpc = fake_node(chain_id, code, domain, *behavior)
            try:
                builder.check_deployed_profile("http://node", pool, chain_id, logic, verifier)
            except SystemExit as error:
                assert expected in str(error), (label, error)
            else:
                raise AssertionError(f"accepted {label}")
        builder.rpc = fake_node(chain_id, this_code, good)
        builder.check_deployed_profile("http://node", pool, chain_id, logic, verifier)
        # The genuine pool on the RPC's chain is still refused when the config
        # names another chain.
        try:
            builder.check_deployed_profile("http://node", pool, 1, logic, verifier)
        except SystemExit as error:
            assert "config names chain 1" in str(error), error
        else:
            raise AssertionError("accepted an RPC on a different chain")
    finally:
        builder.rpc = real_rpc


def check_cli_runs_deployed_gate():
    """shield, transfer and withdraw refuse the previous profile's pool, relabeled as
    this profile, before anything is signed or sent."""
    cfg, _, _, _, previous_code = recorded_pool()
    pool = int(cfg["pool"], 16)
    good = "0x" + builder.expected_domain(cfg["chainId"], pool).to_bytes(32, "big").hex()
    tmp = tempfile.TemporaryDirectory()
    cfg_path = Path(tmp.name) / "config.json"
    cfg_path.write_text(json.dumps(dict(cfg, profile=POOL_PROFILE)))
    rpc = fake_node(cfg["chainId"], previous_code, good)

    for operation in ("shield", "transfer", "withdraw"):
        argv = ["pool_frametx.py", "http://node", str(cfg_path),
                str(ROOT / "wallet/smoke_fixture.json"), operation, "01" * 32]
        with mock.patch.object(builder, "rpc", rpc), mock.patch.object(sys, "argv", argv), \
                contextlib.redirect_stdout(io.StringIO()):
            try:
                builder.main()
            except SystemExit as error:
                assert f"is not the {POOL_PROFILE} dispatcher" in str(error), (operation, error)
            else:
                raise AssertionError(f"{operation} ran without the deployed-pool check")


def main():
    assert POOL_PROFILE == "position-notes-v2"
    runs = check_profile_labels()
    check_recorded_deployment()
    check_deployed_pool_gate()
    check_cli_runs_deployed_gate()
    print(f"PASS: other, null and missing profile labels rejected before RPC in {runs} CLI runs; "
          "recorded deployment matches the domain formula; the previous profile's dispatcher, "
          "other logic or verifier, a verifier that does not verify this profile's proofs, "
          "codeless, wrong-domain and wrong-chain pools refused; "
          "shield, transfer and withdraw refuse a relabeled previous-profile pool before sending")


if __name__ == "__main__":
    main()
