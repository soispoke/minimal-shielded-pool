#!/usr/bin/env python3
"""The activation gate must reject malformed or self-certified manifests and mismatched setups."""
import copy
import json
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import check_activation as gate  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
CHECK = ROOT / "tools/check_activation.py"
BASE = json.loads((ROOT / "core/activation_manifest.testbed.json").read_text())


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


def setup_rejected(message, r1cs=None, zkey=None, verifier=None):
    """check_setup must reject the committed artifacts with one of them replaced."""
    with tempfile.TemporaryDirectory() as tmp:
        paths = []
        for rel, content in ((gate.R1CS, r1cs), (gate.ZKEY, zkey), (gate.VERIFIER, verifier)):
            path = ROOT / rel
            if content is not None:
                path = Path(tmp) / path.name
                path.write_bytes(content)
            paths.append(path)
        try:
            gate.check_setup(*paths)
        except SystemExit as err:
            assert message in str(err), (message, str(err))
        else:
            raise AssertionError(f"check_setup accepted a mismatched setup: {message}")


def setup_cases():
    """A key, R1CS or verifier that honest proofs cannot tell apart must still fail."""
    zkey = bytearray((ROOT / gate.ZKEY).read_bytes())
    _, found = gate.sections(ROOT / gate.ZKEY, b"zkey", 4)
    zkey[found[4] + 4 + 12] ^= 1  # the first A coefficient

    # A circuit with one fewer constraint than the key was set up from.
    r1cs = bytearray((ROOT / gate.R1CS).read_bytes())
    _, found = gate.sections(ROOT / gate.R1CS, b"r1cs", 1)
    at = found[1] + 4 + struct.unpack_from("<I", r1cs, found[1])[0] + 24
    struct.pack_into("<I", r1cs, at, struct.unpack_from("<I", r1cs, at)[0] - 1)

    verifier = (ROOT / gate.VERIFIER).read_text()
    assert verifier.count("deltax1 = ") == 1
    cases = (
        ("A/B terms", {"zkey": bytes(zkey)}),
        ("A/B terms", {"r1cs": bytes(r1cs)}),
        ("deltax1", {"verifier": verifier.replace("deltax1 = ", "deltax1 = 1").encode()}),
    )
    for message, replaced in cases:
        setup_rejected(message, **replaced)
    return len(cases)


def main():
    assert run(BASE, "--allow-testbed").returncode == 0
    blocked = run(BASE)
    assert blocked.returncode != 0 and "testbed-only" in blocked.stderr, blocked.stderr

    cases = {
        "empty artifacts": (lambda m: m.update(artifacts={}), "required artifacts"),
        "missing proving key": (lambda m: m["artifacts"].pop("core/artifacts/spend_final.zkey"),
                                "core/artifacts/spend_final.zkey"),
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

    # --ptau runs snarkjs only on a file whose hash the manifest pins.
    unpinned = (BASE, "requires ceremony.phase1_ptau_sha256")
    wrong = (mutated(ceremony(phase1_ptau_sha256="0" * 64)), "ptau hash does not match")
    for manifest, message in (unpinned, wrong):
        result = run(manifest, "--allow-testbed", "--ptau", str(ROOT / gate.R1CS))
        assert result.returncode != 0 and message in result.stderr, result.stderr

    mismatches = setup_cases()
    print(f"PASS: testbed manifest gated; {len(cases)} malformed or self-certified manifests, "
          f"2 unpinned ptau files and {mismatches} mismatched key setups rejected")


if __name__ == "__main__":
    main()
