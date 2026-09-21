#!/usr/bin/env python3
"""Rebuild vectors and run the native gas-action evidence suite."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def run(command, *, env=None):
    print("+", " ".join(map(str, command)), flush=True)
    subprocess.run([str(item) for item in command], cwd=REPO, env=env, check=True)


def verify_ethrex(source):
    expected = json.loads((HERE / "ethrex-source-sha256.json").read_text())
    for relative, digest in expected.items():
        path = source / relative
        observed = hashlib.sha256(path.read_bytes()).hexdigest()
        if observed != digest:
            raise SystemExit(f"pinned ethrex source mismatch: {relative}: {observed}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--ethrex-source",
        default=os.environ.get("ETHREX_SOURCE"),
        help="ethrex 247e2dd2 source snapshot (or set ETHREX_SOURCE)",
    )
    parser.add_argument("--offline", action="store_true", help="pass --offline to cargo")
    parser.add_argument("--skip-generate", action="store_true", help="run committed vectors only")
    args = parser.parse_args()
    if not args.ethrex_source:
        raise SystemExit("--ethrex-source or ETHREX_SOURCE is required")
    source = Path(args.ethrex_source).resolve()
    verify_ethrex(source)

    if not args.skip_generate:
        run(["forge", "build", "--root", "contracts", "--force"])
        small = dict(os.environ)
        small["FOUNDRY_PROFILE"] = "libsmall"
        run(["forge", "build", "--root", "contracts", "--force"], env=small)
        run(["python3", HERE / "scripts" / "compile_fixtures.py"])
        run(["python3", HERE / "scripts" / "generate_fixtures.py"])

    manifest = (HERE / "Cargo.toml.in").read_text().replace("@ETHREX@", str(source))
    (HERE / "Cargo.toml").write_text(manifest)
    environment = dict(os.environ)
    environment["ETHREX_SOURCE"] = str(source)
    command = ["cargo", "test", "--locked", "--manifest-path", HERE / "Cargo.toml"]
    if args.offline:
        command.insert(2, "--offline")
    command += ["--", "--nocapture"]
    run(command, env=environment)


if __name__ == "__main__":
    main()
