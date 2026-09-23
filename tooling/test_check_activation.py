#!/usr/bin/env python3
"""The activation gate must reject malformed or self-certified manifests."""
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECK = ROOT / "tooling/check_activation.py"
BASE = json.loads((ROOT / "activation_manifest.testbed.json").read_text())


def run(manifest, *flags):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps(manifest))
        return subprocess.run([sys.executable, str(CHECK), str(path), *flags],
                              capture_output=True, text=True)


def mutated(change):
    manifest = copy.deepcopy(BASE)
    change(manifest)
    return manifest


def ceremony(**fields):
    return lambda m: m["ceremony"].update(fields)


def main():
    assert run(BASE, "--allow-testbed").returncode == 0
    blocked = run(BASE)
    assert blocked.returncode != 0 and "testbed-only" in blocked.stderr, blocked.stderr

    cases = {
        "empty artifacts": (lambda m: m.update(artifacts={}), "required artifacts"),
        "missing proving key": (lambda m: m["artifacts"].pop("build/spend_final.zkey"),
                                "build/spend_final.zkey"),
        "string production": (lambda m: m.update(production="false"), "JSON boolean"),
        "string contribution count": (ceremony(phase2_contributions="1"), "JSON integer"),
        "boolean contribution count": (ceremony(phase2_contributions=True), "JSON integer"),
        "string verification": (ceremony(independent_verification="false"), "boolean or null"),
        "overstated contributions": (lambda m: (m.update(production=True), m["ceremony"].update(
            phase2_contributions=2, independent_verification=True)), "does not match the proving key"),
        "production without ceremony": (lambda m: (m.update(production=True), m["ceremony"].update(
            independent_verification=True)), "ceremony evidence is incomplete"),
    }
    for label, (change, message) in cases.items():
        for flags in ((), ("--allow-testbed",)):
            result = run(mutated(change), *flags)
            assert result.returncode != 0, (label, flags)
            assert message in result.stderr, (label, result.stderr)
    print(f"PASS: testbed manifest gated; {len(cases)} malformed or self-certified manifests rejected")


if __name__ == "__main__":
    main()
