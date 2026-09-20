#!/usr/bin/env python3
"""Run the signed native-client fixtures in a temporary crate outside the repo."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
COMMIT = "247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e"
ARCHIVE_SHA256 = "12de2898010a160bfb45390f7b50ef5b0f1d970a3e1433ad48ed9e542152a414"
ARCHIVE_URL = f"https://codeload.github.com/lambdaclass/ethrex/legacy.tar.gz/{COMMIT}"


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def within(path, parent):
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def verify_files(root, hashes):
    for relative, expected in hashes.items():
        path = root / relative
        if not within(path, root) or not path.is_file() or sha256(path) != expected:
            raise RuntimeError(f"source hash mismatch: {path}")


def client_sources(root):
    return {
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_file() and (path.suffix in (".rs", ".toml") or path.name == "Cargo.lock")
    }


def verify_client(root):
    manifest = json.loads((HERE / "client-source-hashes.json").read_text())
    if manifest["commit"] != COMMIT:
        raise RuntimeError("client hash manifest uses a different commit")
    expected = manifest["files"]
    observed = client_sources(root)
    if observed != set(expected):
        missing = sorted(set(expected) - observed)
        extra = sorted(observed - set(expected))
        raise RuntimeError(f"client source file set differs: missing={missing[:5]}, extra={extra[:5]}")
    verify_files(root, expected)


def extract_archive(archive, destination):
    """Extract verified source without permitting path or link escapes."""
    with tarfile.open(archive, "r:gz") as source:
        members = source.getmembers()
        roots = {PurePosixPath(member.name).parts[0] for member in members if member.name}
        if len(roots) != 1:
            raise RuntimeError("client archive must have one top-level directory")
        top = destination / roots.pop()
        for member in members:
            parts = PurePosixPath(member.name).parts
            if not parts or member.name.startswith("/") or ".." in parts:
                raise RuntimeError(f"unsafe archive path: {member.name}")
            target = destination.joinpath(*parts)
            if not within(target, top):
                raise RuntimeError(f"archive path escapes source: {member.name}")
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                with source.extractfile(member) as incoming, target.open("wb") as outgoing:
                    shutil.copyfileobj(incoming, outgoing)
                target.chmod(member.mode & 0o777)
            elif member.issym():
                if Path(member.linkname).is_absolute() or not within(target.parent / member.linkname, top):
                    raise RuntimeError(f"unsafe archive symlink: {member.name}")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(member.linkname)
            else:
                raise RuntimeError(f"unsupported archive entry: {member.name}")
    return top


def client_source(cache, offline):
    configured = os.environ.get("ETHREX_SOURCE")
    if configured:
        root = Path(configured).expanduser().resolve()
    else:
        root = cache / f"ethrex-{COMMIT}"
        if not root.exists():
            if offline:
                raise RuntimeError("offline run requires ETHREX_SOURCE or a cached pinned client")
            archive = cache / f"ethrex-{COMMIT}.tar.gz"
            if not archive.exists() or sha256(archive) != ARCHIVE_SHA256:
                request = urllib.request.Request(ARCHIVE_URL, headers={"User-Agent": "minimal-shielded-pool-native-test"})
                with urllib.request.urlopen(request, timeout=120) as response, archive.open("wb") as output:
                    shutil.copyfileobj(response, output)
            if sha256(archive) != ARCHIVE_SHA256:
                raise RuntimeError(f"downloaded client archive has the wrong SHA256: {archive}")
            with tempfile.TemporaryDirectory(prefix="extract-", dir=cache) as temporary:
                extracted = extract_archive(archive, Path(temporary))
                verify_client(extracted)
                extracted.rename(root)
    verify_client(root)
    return root


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="use cached client and Cargo dependencies")
    parser.add_argument("--check-inputs", action="store_true", help="only verify fixture source hashes")
    arguments = parser.parse_args()
    # The transaction fixtures embed deployed production artifacts. Refuse to
    # report success against stale fixtures after those production sources change.
    pool_hashes = json.loads((HERE / "pool-source-hashes.json").read_text())
    verify_files(REPO, pool_hashes)
    if arguments.check_inputs:
        print(f"Verified {len(pool_hashes)} fixture source hashes")
        return
    cache = Path(tempfile.gettempdir()) / "msp-native-recipient-pull-cache"
    cache.mkdir(parents=True, exist_ok=True)
    source = client_source(cache, arguments.offline)
    configured_workdir = os.environ.get("NATIVE_WORKDIR")
    workdir = (Path(configured_workdir).expanduser().resolve() if configured_workdir
               else Path(tempfile.mkdtemp(prefix="run-", dir=cache)))
    if within(workdir, REPO):
        raise RuntimeError("NATIVE_WORKDIR must be outside the repository")
    workdir.mkdir(parents=True, exist_ok=True)
    shutil.copytree(HERE / "src", workdir / "src", dirs_exist_ok=True)
    shutil.copytree(HERE / "fixtures", workdir / "fixtures", dirs_exist_ok=True)
    shutil.copy2(HERE / "Cargo.lock", workdir / "Cargo.lock")
    template = (HERE / "Cargo.toml.in").read_text()
    for marker, relative in (("__ETHREX_LEVM__", "crates/vm/levm"),
                             ("__ETHREX_COMMON__", "crates/common"),
                             ("__ETHREX_CRYPTO__", "crates/common/crypto")):
        template = template.replace(marker, json.dumps(str(source / relative)))
    (workdir / "Cargo.toml").write_text(template)
    environment = os.environ.copy()
    environment["ETHREX_SOURCE"] = str(source)
    target = Path(environment.get("CARGO_TARGET_DIR", str(cache / "target"))).expanduser().resolve()
    if within(target, REPO):
        raise RuntimeError("CARGO_TARGET_DIR must be outside the repository")
    environment["CARGO_TARGET_DIR"] = str(target)
    environment.setdefault("NATIVE_REPORT", str(workdir / "native-report.json"))
    command = [environment.get("CARGO_BIN", "cargo"), "test", "--manifest-path", str(workdir / "Cargo.toml"), "--locked"]
    if arguments.offline:
        command.append("--offline")
    command.extend(["--", "--nocapture"])
    print(f"Pinned client: {source}", flush=True)
    print(f"Native work directory: {workdir}", flush=True)
    print(f"Native report: {environment['NATIVE_REPORT']}", flush=True)
    subprocess.run(command, cwd=workdir, env=environment, check=True)


if __name__ == "__main__":
    main()
