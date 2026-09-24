#!/usr/bin/env python3
"""The deployment script's code checks must reject every mismatch and failed read.

run_live_dispatcher.sh calls each check on the left of `||`, where Bash ignores
`set -e`. This runs the script's own functions that way, against a fake `cast`,
so a check whose failure is overwritten by a later line is caught here.
"""
import json
import os
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
    print(f"PASS: {len(cases)} deployment-check cases; mismatched code, wrong Poseidon addresses "
          "and failed reads are rejected even when an earlier line fails and a later one passes")


if __name__ == "__main__":
    main()
