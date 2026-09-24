#!/usr/bin/env python3
"""The deployment script's code checks must reject every mismatch and failed read.

run_live_dispatcher.sh calls each check on the left of `||`, where Bash ignores
`set -e`. This runs the script's own functions that way, against a fake `cast`,
so a check whose failure is overwritten by a later line is caught here.
"""
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "run_live_dispatcher.sh"
T3, T4 = "0x00000000000000000000000000000000000000A3", "0x00000000000000000000000000000000000000A4"
LIB = "0x00000000000000000000000000000000000000b1"
LIB_CODE = "0x73" + LIB[2:] + "3014"
LOGIC_CODE = "0x60016002"
POOL_CODE = "0x6005"

FAKE_CAST = '''
cast() {
  local out status
  case "$1 $2 $3" in
    code*) out=$CODE status=${CODE_STATUS:-0} ;;
    "call --rpc-url"*) out=$CREATED status=${CREATED_STATUS:-0} ;;
    *POSEIDON_T3*) out=$GOT_T3 status=${T3_STATUS:-0} ;;
    *POSEIDON_T4*) out=$GOT_T4 status=${T4_STATUS:-0} ;;
    *) return 2 ;;
  esac
  printf '%s\\n' "$out"
  return "$status"
}
'''


def function(source, name):
    start = source.index(f"{name}() {{")
    return source[start:source.index("\n}\n", start) + 3]


def accepts(call, env):
    source = SCRIPT.read_text()
    functions = "".join(function(source, name) for name in (
        "verify_library_runtime", "verify_logic_runtime", "verify_created_runtime"))
    program = (f"set -euo pipefail\nRPC=offline\nT3={T3}\nT4={T4}\n{FAKE_CAST}{functions}"
               f"{call} || {{ echo REJECT; exit 7; }}\necho ACCEPT\n")
    result = subprocess.run(["bash", "-c", program], env={**os.environ, **env},
                            capture_output=True, text=True)
    assert result.stdout in ("ACCEPT\n", "REJECT\n"), (call, env, result.stdout, result.stderr)
    return result.stdout == "ACCEPT\n"


CHECKS = ("verify_library_runtime", "verify_logic_runtime", "verify_created_runtime")


def call_sites():
    """Each check is defined once, and every call refuses the deployment when it
    fails; no inline comparison of two command substitutions remains."""
    source = SCRIPT.read_text()
    lines = source.splitlines()
    calls = 0
    for name in CHECKS:
        assert source.count(f"{name}() {{") == 1, f"{name} must be defined exactly once"
        for i, line in enumerate(lines):
            if line.startswith(f"{name} "):
                block = "\n".join(lines[i:i + 4])
                assert "|| {" in line and "exit 1" in block[:block.index("}") + 1], line
                calls += 1
    assert calls == 4, calls
    assert not re.search(r"\[\[ *\$\(.*\) *== *\$\(", source), "inline comparison of two reads"
    return calls


def early_guards():
    """The script stops before calling cast or forge when a FOUNDRY_* variable
    would change what forge builds, or when its fixture path already exists."""
    checked = 0
    with tempfile.TemporaryDirectory() as tmp:
        bin_dir = Path(tmp, "bin")
        bin_dir.mkdir()
        for tool in ("cast", "forge"):
            fake = bin_dir / tool
            fake.write_text("#!/bin/sh\necho REACHED >&2\nexit 99\n")
            fake.chmod(0o755)
        base = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}", "RPC_URL": "offline",
                "DEPLOYER_PK": "0x01", "ALLOW_TESTBED_SETUP": "1", "SMOKE_OUTPUT": str(Path(tmp, "new.json"))}
        existing = Path(tmp, "existing.json")
        existing.write_text("{}")
        for extra, expected in (({"SMOKE_OUTPUT": str(existing)}, "may hold the only secrets"),
                                ({"FOUNDRY_VIA_IR": "false"}, "unset FOUNDRY_VIA_IR"),
                                ({"DAPP_SRC": "src"}, "unset DAPP_SRC")):
            env = {k: v for k, v in base.items() if not k.startswith(("FOUNDRY_", "DAPP_"))}
            result = subprocess.run(["bash", str(SCRIPT)], env={**env, **extra},
                                    capture_output=True, text=True)
            assert result.returncode == 1 and expected in result.stderr, (extra, result.stderr[-400:])
            assert "REACHED" not in result.stderr, extra
            checked += 1
    return checked


def main():
    with tempfile.TemporaryDirectory() as tmp:
        artifact = Path(tmp, "out/ShieldedPoolLogic.sol/ShieldedPoolLogic.json")
        artifact.parent.mkdir(parents=True)
        # Byte 1 holds an immutable, so it may differ from the simulated deployment.
        artifact.write_text(json.dumps(
            {"deployedBytecode": {"immutableReferences": {"7": [{"start": 1, "length": 1}]}}}))
        logic = {"BN": tmp, "CODE": LOGIC_CODE, "GOT_T3": T3, "GOT_T4": T4}
        library = {"CODE": LIB_CODE}
        pool = {"CODE": POOL_CODE, "CREATED": POOL_CODE}
        cases = [
            ("library", library, True),
            ("library", dict(library, CODE=LIB_CODE[:-1] + "5"), False),
            ("library", dict(library, CODE="0x73" + "00" * 20 + "3014"), False),
            ("library", dict(library, CODE_STATUS="1"), False),
            ("logic", logic, True),
            ("logic", dict(logic, CODE="0x60ff6002"), True),
            ("logic", dict(logic, CODE="0x60016003"), False),
            ("logic", dict(logic, CODE="0x600160"), False),
            ("logic", dict(logic, GOT_T3=T4), False),
            ("logic", dict(logic, GOT_T4=T3), False),
            ("logic", dict(logic, CODE_STATUS="1"), False),
            ("logic", dict(logic, T3_STATUS="1"), False),
            ("logic", dict(logic, T4_STATUS="1"), False),
            ("pool", pool, True),
            ("pool", dict(pool, CODE="0x6006"), False),
            ("pool", dict(pool, CODE="0x", CREATED="0x"), False),
            ("pool", dict(pool, CODE_STATUS="1"), False),
            ("pool", dict(pool, CREATED_STATUS="1"), False),
            ("pool", dict(pool, CODE="", CREATED="", CODE_STATUS="1", CREATED_STATUS="1"), False),
        ]
        calls = {"library": f"verify_library_runtime {LIB} {LIB_CODE}",
                 "logic": f"verify_logic_runtime 0x01 {LOGIC_CODE}",
                 "pool": "verify_created_runtime 0x02 0xinit"}
        for kind, env, expected in cases:
            assert accepts(calls[kind], env) == expected, (kind, env)
    calls = call_sites()
    guards = early_guards()
    print(f"PASS: {len(cases)} deployment-check cases; mismatched code, wrong Poseidon addresses "
          "and failed reads are rejected even when an earlier line fails and a later one passes; "
          f"{calls} call sites refuse on failure; {guards} early guards stop before cast or forge")


if __name__ == "__main__":
    main()
