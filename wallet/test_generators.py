#!/usr/bin/env python3
"""The fixture generators refuse, before proving, anything that would put live
notes at risk: the public seed off the test chain, a recipient that strands its
credit, and overwriting a fixture that may hold the only secrets of unspent
notes. Their secrets are written readable by the owner only.
Run: python3 wallet/test_generators.py."""
import http.server
import json
import os
import stat
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_nonce_race  # noqa: E402
import gen_smoke  # noqa: E402
import wallet as w  # noqa: E402

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
        # The final write refuses a fixture that appeared, or was replaced by
        # another run, since the overwrite check.
        try:
            gen_smoke.write_private(fresh, "other", None)
        except SystemExit as error:
            assert "appeared while generating" in str(error)
        else:
            raise AssertionError("a new fixture replaced one that appeared meanwhile")
        test_fixture = Path(tmp, "test.json")
        test_fixture.write_text(json.dumps({"chain_id": gen_smoke.TEST_CHAIN_ID}))
        previous = gen_smoke.refuse_overwrite(test_fixture)
        test_fixture.write_text(json.dumps({"chain_id": 8141, "secrets": "another run"}))
        try:
            gen_smoke.write_private(test_fixture, "mine", previous)
        except SystemExit as error:
            assert "changed while generating" in str(error)
        else:
            raise AssertionError("a fixture replaced another run's")
        assert "another run" in test_fixture.read_text()
        assert not [n for n in os.listdir(tmp) if n.startswith(".")], "temporary file left behind"
        checked += 4

        # Live fixtures default to the ignored artifacts directory.
        assert gen_smoke.default_output(31337, gen_smoke.TEST_POOL) == HERE / "smoke_fixture.json"
        for live in (gen_smoke.default_output(8141, gen_smoke.TEST_POOL), gen_nonce_race.DEFAULT_OUTPUT):
            assert live.parent == gen_smoke.WORK, live
            ignored = subprocess.run(["git", "check-ignore", "-q", str(live)], cwd=HERE)
            assert ignored.returncode == 0, f"{live} is not ignored"
        checked += 1

        # A nonce-race fixture records what recovery and the shield check need:
        # each transfer's output openings and each shield's prior root.
        race_out = Path(tmp, "race.json")
        gen_smoke.WORK.mkdir(exist_ok=True)
        work_before = set(os.listdir(gen_smoke.WORK))
        result = subprocess.run([sys.executable, str(HERE / "gen_nonce_race.py"), "--chain-id=31337", *race,
                                 f"--output={race_out}"], cwd=HERE, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr[-500:]
        # Each proof ran in its own directory, removed afterwards with the
        # witness it held, so concurrent runs cannot swap proofs.
        assert set(os.listdir(gen_smoke.WORK)) == work_before, "proving left files behind"
        fixture = json.loads(race_out.read_text())
        for name in ("transfer", "transfer_c"):
            entry = fixture[name]
            cms = [w.commitment(int(o["spend_key"], 16), int(o["rho"], 16), int(o["value"]))
                   for o in entry["output_openings"]]
            assert cms == [int(entry["out_cm1"], 16), int(entry["out_cm2"], 16)], name
        tree = w.Tree()
        for shield in fixture["shields"]:
            assert int(shield["prior_root"], 16) == tree.root(), shield["leaf"]
            assert tree.append(int(shield["cm"], 16)) == shield["leaf"]
        checked += 1

        # With --rpc, the chain it reads must be the one named.
        class Chain(http.server.BaseHTTPRequestHandler):
            def do_POST(self):
                self.rfile.read(int(self.headers["Content-Length"]))
                body = json.dumps({"jsonrpc": "2.0", "id": 1, "result": "0x1"}).encode()
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *args):
                pass
        server = http.server.HTTPServer(("127.0.0.1", 0), Chain)
        threading.Thread(target=server.serve_forever, daemon=True).start()
        try:
            checked += refused("gen_nonce_race.py", ["--random", "--chain-id=8141", *race,
                                                     f"--rpc=http://127.0.0.1:{server.server_port}",
                                                     "--pool=0x01", f"--output={tmp}/rpc.json"],
                               "does not match the chain")
        finally:
            server.shutdown()
    print(f"PASS: {checked} generator refusals and secret-file checks")


if __name__ == "__main__":
    main()
