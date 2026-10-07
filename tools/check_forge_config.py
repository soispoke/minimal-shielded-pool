#!/usr/bin/env python3
"""Refuse to build deployment bytecode with compiler settings nobody reviewed.

forge resolves its settings from foundry.toml, FOUNDRY_* variables in any
letter case, .env files and the global ~/.foundry/foundry.toml, and it fills
in defaults such as evm_version from its own version. The deployment checks
compare the chain with that same local build, so they cannot notice a change.
This asks forge what it would actually use, in the caller's environment, and
compares that with the settings the activation manifest pins.

Usage: check_forge_config.py MANIFEST CONTRACTS_ROOT
"""
import json
import os
import subprocess
import sys

KEYS = ("solc", "optimizer", "optimizer_runs", "optimizer_details", "via_ir", "evm_version",
        "bytecode_hash", "cbor_metadata", "use_literal_content", "revert_strings", "libraries",
        "remappings")


def resolved(root, profile):
    """The settings forge would use. The default profile runs in the caller's
    environment unchanged, as the deployment's plain forge calls do."""
    env = dict(os.environ)
    if profile != "default":
        env["FOUNDRY_PROFILE"] = profile
    result = subprocess.run(["forge", "config", "--root", root, "--json"], env=env,
                            capture_output=True, text=True)
    if result.returncode != 0:
        raise SystemExit(f"forge config failed for profile {profile}: {result.stderr.strip()}")
    config = json.loads(result.stdout)
    return {key: config.get(key) for key in KEYS}


def main():
    manifest, root = sys.argv[1], sys.argv[2]
    with open(manifest) as f:
        pinned = json.load(f)["compiler"]
    for profile, expected in pinned.items():
        actual = resolved(root, profile)
        drift = [f"{key}={actual[key]!r} (pinned {expected.get(key)!r})"
                 for key in KEYS if actual[key] != expected.get(key)]
        if drift:
            raise SystemExit(f"forge resolves profile {profile} differently from the manifest: "
                             + ", ".join(drift))
    print(json.dumps({"compiler": "match", "profiles": sorted(pinned)}))


if __name__ == "__main__":
    main()
