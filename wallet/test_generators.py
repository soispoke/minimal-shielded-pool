#!/usr/bin/env python3
"""The fixture generators refuse, before proving, anything that would put live
notes at risk: the public seed off the test chain, a recipient that strands its
credit, and overwriting a fixture that may hold the only secrets of unspent
notes. Their secrets are written readable by the owner only.
Run: python3 wallet/test_generators.py."""
import json
import os
import stat
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_smoke  # noqa: E402

LIVE = ["--chain-id=8141", "--pool-address=0x1111111111111111111111111111111111111111"]
RECIPIENT = "--recipient=0x00000000000000000000000000000000000000ff"


def refused(script, args, expected):
    result = subprocess.run([sys.executable, str(HERE / script), *args],
                            cwd=HERE, capture_output=True, text=True)
    assert result.returncode != 0 and expected in result.stderr, (script, args, result.stderr[-500:])
    return 1


def main():
    checked = 0
    with tempfile.TemporaryDirectory() as tmp:
        out = f"--output={tmp}/fixture.json"
        live_fixture = Path(tmp, "live.json")
        live_fixture.write_text(json.dumps({"chain_id": 8141}))
        over_live = f"--output={live_fixture}"
        checked += refused("gen_smoke.py", [*LIVE, RECIPIENT, out], "fixed seed is public")
        checked += refused("gen_smoke.py", ["--random", *LIVE, out], "test placeholder")
        for stranding in ("0x0000000000000000000000000000000000000001",
                          "0x0000000000000000000000000000000000008250",
                          "0x1111111111111111111111111111111111111111"):
            checked += refused("gen_smoke.py", ["--random", *LIVE, f"--recipient={stranding}", out],
                               "would strand the withdrawal credit")
        checked += refused("gen_smoke.py", ["--random", *LIVE, RECIPIENT, over_live], "holds a fixture for chain 8141")
        checked += refused("gen_smoke.py", [over_live], "holds a fixture for chain 8141")
        race = ["--pool-address=0x1111111111111111111111111111111111111111", "--root-slot=5"]
        checked += refused("gen_nonce_race.py", ["--chain-id=8141", *race, out], "fixed seed is public")
        checked += refused("gen_nonce_race.py", ["--chain-id=31337", *race, "--rpc=http://127.0.0.1:1",
                                                 "--pool=0x01", out], "fixed seed is public")
        checked += refused("gen_nonce_race.py", ["--random", "--chain-id=8141", *race, over_live],
                           "holds a fixture for chain 8141")

        # A new secret file is owner-only, and replacing an old world-readable
        # one gives a new file, so a reader holding the old one open sees none of it.
        target = Path(tmp, "witness.json")
        target.write_text("old")
        target.chmod(0o644)
        before = target.stat().st_ino
        with open(target) as held:
            gen_smoke.write_private(target, "secret")
            assert held.read() == "old"
        assert target.read_text() == "secret" and target.stat().st_ino != before
        assert stat.S_IMODE(target.stat().st_mode) == 0o600
        fresh = Path(tmp, "fresh.json")
        gen_smoke.write_private(fresh, "secret")
        assert stat.S_IMODE(fresh.stat().st_mode) == 0o600
        # An exclusive write refuses a file that appeared since the check.
        try:
            gen_smoke.write_private(fresh, "other", exclusive=True)
        except SystemExit as error:
            assert "appeared while generating" in str(error)
        else:
            raise AssertionError("exclusive write replaced an existing fixture")
        assert fresh.read_text() == "secret"
        assert not [n for n in os.listdir(tmp) if n.startswith(".")], "temporary file left behind"
        checked += 3
    print(f"PASS: {checked} generator refusals and secret-file checks")


if __name__ == "__main__":
    main()
