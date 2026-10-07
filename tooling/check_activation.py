#!/usr/bin/env python3
"""Fail-closed artifact, ceremony, and gas-profile activation gate."""
import argparse
import hashlib
import json
import re
import struct
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "devnet"))

from gas_profile import (  # noqa: E402
    CLAIM_FRAME_GAS,
    CLAIM_FRAME_STATE_GAS,
    POOL_PROFILE,
    RECENT_ROOT_FRAME_GAS,
    SETTLE_FRAME_GAS,
    SETTLE_FRAME_STATE_GAS,
    VERIFY_FRAME_GAS,
    VERIFY_FRAME_STATE_GAS,
)

# The settlement budgets each supported wire profile is allowed to declare, keyed by
# the manifest's `wire_profile`. An unlisted profile is rejected: the gate stays
# fail-closed, and adding a dialect means adding its budgets here deliberately rather
# than letting a manifest name its own.
#
# Split profiles declare execution and state independently. Historical budgets
# stay frozen here; position-notes-v1 pins settlement execution at 2M because
# native spends at 262,143 and 524,287 leaves OOG at 1.4M after VERIFY and
# approval succeed. State remains 550,000. 2M is the reproduced fix, not a
# proof of every settlement shape.
PROFILES = {
    "ethrex-v23-hegota-testnet": {
        "verify_frame_gas": 320_000,
        "signature_gas": 2_800,
        "verify_frame_state_gas": None,
        "settle_frame_gas": 2_000_000,
        "settle_frame_state_gas": None,
    },
    "ethrex-v23-spec-2026-08-31": {
        "verify_frame_gas": 320_000,
        "signature_gas": 2_800,
        "verify_frame_state_gas": 0,
        "settle_frame_gas": 1_400_000,
        "settle_frame_state_gas": 550_000,
    },
    "eip8250-state-gas-pre-8272-frame": {
        "verify_frame_gas": 320_000,
        "signature_gas": 2_800,
        "verify_frame_state_gas": 195_840,
        "settle_frame_gas": 1_400_000,
        "settle_frame_state_gas": 550_000,
    },
    # EIP-8272 at 824cbc0b0e: the recent root travels in a canonical verifier frame that
    # leads the transaction and counts toward the verify budget.
    "eip8272-canonical-frame": {
        "recent_root_frame_gas": 30_000,
        "verify_frame_gas": 320_000,
        "signature_gas": 2_800,
        "verify_frame_state_gas": 195_840,
        "settle_frame_gas": 1_400_000,
        "settle_frame_state_gas": SETTLE_FRAME_STATE_GAS,
    },
    # Withdrawals add an exact DEFAULT claim frame. A 3-frame eip8272-canonical-frame
    # pool is not compatible with this wallet.
    "recipient-pull-v1": {
        "recent_root_frame_gas": 30_000,
        "verify_frame_gas": 320_000,
        "signature_gas": 2_800,
        "verify_frame_state_gas": 195_840,
        "settle_frame_gas": 1_400_000,
        "settle_frame_state_gas": SETTLE_FRAME_STATE_GAS,
        "pool_profile": "recipient-pull-v1",
        "claim_frame_gas": CLAIM_FRAME_GAS,
        "claim_frame_state_gas": CLAIM_FRAME_STATE_GAS,
    },
}

# Same frame grammar plus an optional generic DEFAULT tail, new
# circuit/nullifier identities and storage layout. Fresh deployment required.
PROFILES["position-notes-v1"] = {
    **PROFILES["recipient-pull-v1"], "pool_profile": "position-notes-v1",
    "settle_frame_gas": SETTLE_FRAME_GAS,
}

# The dispatcher stops pinning the validation frames' limits. These are the wallet
# defaults the manifest records, sized from measurement with headroom.
PROFILES["position-notes-v2"] = {
    **PROFILES["position-notes-v1"], "pool_profile": "position-notes-v2",
    "recent_root_frame_gas": RECENT_ROOT_FRAME_GAS,
    "verify_frame_gas": VERIFY_FRAME_GAS,
    "verify_frame_state_gas": VERIFY_FRAME_STATE_GAS,
}
# Same budgets; settlement and shield carry notes, so the wire format changes and a
# fresh deployment is required.
PROFILES["position-notes-v3"] = {**PROFILES["position-notes-v2"], "pool_profile": POOL_PROFILE}


# Every active artifact must be pinned. A manifest that omits one would
# otherwise pass without its hash being checked. foundry.toml is pinned here;
# check_forge_config.py compares the settings forge actually resolves, which
# environment variables, .env files and the global config can also change.
REQUIRED_ARTIFACTS = (
    "build/spend.r1cs",
    "build/spend_final.zkey",
    "build/spend_js/spend.wasm",
    "circuits/spend.circom",
    "contracts/foundry.toml",
    "contracts/src/Groth16Verifier.sol",
    "contracts/src/PoseidonT3.sol",
    "contracts/src/PoseidonT4.sol",
    "contracts/src/ShieldedPoolLogic.sol",
    "devnet/ShieldedPoolDispatcher.yul",
    "devnet/build/shielded_pool_dispatcher_init.hex",
    "devnet/frametx.py",
    "devnet/gas_profile.py",
    "devnet/pool_frametx.py",
    "tooling/check_gas_profile.py",
)
R1CS = "build/spend.r1cs"
ZKEY = "build/spend_final.zkey"
VERIFIER = "contracts/src/Groth16Verifier.sol"
SNARKJS = ROOT / "tooling/node_modules/.bin/snarkjs"


def sections(path, magic, *needed):
    """The file's bytes and the start of each section of an iden3 binary file."""
    data = path.read_bytes()
    if data[:4] != magic:
        raise SystemExit(f"{path} is not a {magic.decode()} file")
    found, offset = {}, 12
    for _ in range(struct.unpack_from("<I", data, 8)[0]):
        # circom declares five r1cs sections and writes three.
        if offset == len(data):
            break
        kind, size = struct.unpack_from("<IQ", data, offset)
        if kind in found:
            raise SystemExit(f"{path} repeats section {kind}")
        found[kind] = offset + 12
        offset += 12 + size
    missing = [kind for kind in needed if kind not in found]
    if missing:
        raise SystemExit(f"{path} has no section {missing[0]}")
    return data, found


def zkey_contributions(path):
    """The phase-2 contribution count a snarkjs zkey records in section 10."""
    data, found = sections(path, b"zkey", 10)
    return struct.unpack_from("<I", data, found[10] + 64)[0]


def r1cs_terms(path):
    """The R1CS field and sizes, and its A and B terms as snarkjs writes them to zkey section 4."""
    data, found = sections(path, b"r1cs", 1, 2)
    n8 = struct.unpack_from("<I", data, found[1])[0]
    prime = int.from_bytes(data[found[1] + 4:found[1] + 4 + n8], "little")
    n_vars, n_out, n_pub_in, _, _, n_constraints = struct.unpack_from("<IIIIQI", data, found[1] + 4 + n8)
    n_public = n_out + n_pub_in
    # snarkjs stores a coefficient v as v * R^2 mod r, with R = 2^256 for BN254.
    r2 = pow(2, 16 * n8, prime)
    terms, offset = [], found[2]
    for constraint in range(n_constraints):
        for matrix in range(3):  # A, B, C; the zkey keeps no C terms
            count = struct.unpack_from("<I", data, offset)[0]
            offset += 4
            for _ in range(count):
                if matrix < 2:
                    signal = struct.unpack_from("<I", data, offset)[0]
                    value = int.from_bytes(data[offset + 4:offset + 4 + n8], "little")
                    terms.append((matrix, constraint, signal, value * r2 % prime))
                offset += 4 + n8
    # snarkjs appends one A row per public input and the constant wire.
    terms += [(0, n_constraints + s, s, r2) for s in range(n_public + 1)]
    return prime, n_vars, n_public, terms


def zkey_setup(path):
    """A snarkjs Groth16 zkey's field and sizes, verification key and section 4 terms."""
    data, found = sections(path, b"zkey", 2, 3, 4)
    offset = found[2]
    n8q = struct.unpack_from("<I", data, offset)[0]
    q = int.from_bytes(data[offset + 4:offset + 4 + n8q], "little")
    offset += 4 + n8q
    n8r = struct.unpack_from("<I", data, offset)[0]
    r = int.from_bytes(data[offset + 4:offset + 4 + n8r], "little")
    offset += 4 + n8r
    n_vars, n_public, _ = struct.unpack_from("<III", data, offset)
    offset += 12

    # Points are affine, with each coordinate x stored as x * 2^256 mod q. A G2
    # point is (x.c0, x.c1, y.c0, y.c1); the verifier names these x2, x1, y2, y1.
    r_inv = pow(2, -8 * n8q, q)

    def coords(at, count):
        return [int.from_bytes(data[at + i * n8q:at + (i + 1) * n8q], "little") * r_inv % q
                for i in range(count)]

    # Section 2 holds alpha1, beta1, beta2, gamma2, delta1, delta2; section 3 holds IC.
    vk = {"r": r, "q": q}
    vk["alphax"], vk["alphay"] = coords(offset, 2)
    for name, at in (("beta", 4), ("gamma", 8), ("delta", 14)):
        x0, x1, y0, y1 = coords(offset + at * n8q, 4)
        vk.update({f"{name}x1": x1, f"{name}x2": x0, f"{name}y1": y1, f"{name}y2": y0})
    for i in range(n_public + 1):
        vk[f"IC{i}x"], vk[f"IC{i}y"] = coords(found[3] + 2 * i * n8q, 2)

    offset, size = found[4] + 4, 12 + n8r
    terms = [(*struct.unpack_from("<III", data, offset + i * size),
              int.from_bytes(data[offset + i * size + 12:offset + (i + 1) * size], "little"))
             for i in range(struct.unpack_from("<I", data, found[4])[0])]
    return r, n_vars, n_public, vk, terms


def check_setup(r1cs, zkey, verifier):
    """Check that the proving key was set up from the R1CS and that the verifier holds its key.

    A key set up from a different R1CS, for example one missing a constraint that
    honest witnesses satisfy anyway, passes every honest-proof test while letting
    anyone prove what the committed circuit forbids. snarkjs copies the A and B
    terms of the R1CS it was given into section 4 and appends one A row per public
    input and the constant wire, so comparing section 4 and the header's nVars and
    nPublic pins the constraint count and every A and B coefficient.

    The C terms exist only inside the IC and L points, and every point is a
    combination of the phase-1 powers of tau. Checking them, or that section 4
    agrees with them, needs the ptau (`--ptau`). This catches a stale key, not one
    built to disagree with its own section 4.
    """
    prime, n_vars, n_public, terms = r1cs_terms(r1cs)
    r, zkey_vars, zkey_public, vk, zkey_terms = zkey_setup(zkey)
    if (r, zkey_vars, zkey_public) != (prime, n_vars, n_public):
        raise SystemExit("proving key field, nVars or nPublic does not match the R1CS")
    if zkey_terms != terms:
        first = next((i for i, pair in enumerate(zip(zkey_terms, terms)) if pair[0] != pair[1]),
                     min(len(zkey_terms), len(terms)))
        raise SystemExit(f"proving key A/B terms do not match the R1CS: {len(zkey_terms)} "
                         f"terms against {len(terms)}, first difference at term {first}")
    constants = {name: int(value) for name, value in
                 re.findall(r"uint256 constant (\w+)\s*=\s*(\d+);", verifier.read_text())}
    wrong = sorted(name for name in constants.keys() | vk.keys() if constants.get(name) != vk.get(name))
    if wrong:
        raise SystemExit(f"verifier constants do not match the proving key: {', '.join(wrong)}")


def verify_with_ptau(ptau, pinned):
    """Run snarkjs's full zkey check against a phase-1 file the manifest pins."""
    if type(pinned) is not str:
        raise SystemExit("--ptau requires ceremony.phase1_ptau_sha256 in the manifest")
    if sha256(ptau) != pinned:
        raise SystemExit("ptau hash does not match ceremony.phase1_ptau_sha256")
    if not SNARKJS.exists():
        raise SystemExit("--ptau requires the pinned snarkjs: npm ci --prefix tooling")
    command = [SNARKJS, "zkey", "verify", ROOT / R1CS, ptau, ROOT / ZKEY]
    result = subprocess.run([str(part) for part in command], capture_output=True, text=True)
    if result.returncode != 0:
        raise SystemExit(f"snarkjs zkey verify failed:\n{result.stdout[-2000:]}{result.stderr[-2000:]}")


def sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--allow-testbed", action="store_true")
    parser.add_argument("--ptau", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())

    artifacts = manifest["artifacts"]
    if not isinstance(artifacts, dict):
        raise SystemExit("artifacts must be a JSON object")
    missing = [rel for rel in REQUIRED_ARTIFACTS if rel not in artifacts]
    if missing:
        raise SystemExit(f"manifest does not pin required artifacts: {', '.join(missing)}")
    for rel, expected in artifacts.items():
        actual = sha256(ROOT / rel)
        if actual != expected:
            raise SystemExit(f"artifact hash mismatch: {rel}\nexpected {expected}\nactual   {actual}")
    # The hashes pin each file; these check that the circuit, key and verifier belong together.
    check_setup(ROOT / R1CS, ROOT / ZKEY, ROOT / VERIFIER)
    if args.ptau:
        verify_with_ptau(args.ptau, manifest["ceremony"].get("phase1_ptau_sha256"))

    profile = manifest["profile"]
    expected = PROFILES.get(profile["wire_profile"])
    if expected is None:
        raise SystemExit(f"unsupported transaction wire profile: {profile['wire_profile']!r}")
    if "claim_frame_gas" in expected:
        for field in ("pool_profile", "claim_frame_gas", "claim_frame_state_gas"):
            if profile.get(field) != expected[field]:
                raise SystemExit(f"{field} does not match the immutable dispatcher profile")
    # A profile with a recent-root verifier frame budgets it in the prefix.
    recent_root_gas = profile.get("recent_root_frame_gas", 0)
    if recent_root_gas != expected.get("recent_root_frame_gas", 0):
        raise SystemExit("recent-root frame gas does not match the immutable dispatcher profile")
    required = recent_root_gas + profile["verify_frame_gas"] + profile["signature_gas"]
    if required != profile["required_verify_budget"]:
        raise SystemExit("required verify budget is inconsistent")
    if profile["verify_frame_gas"] != expected["verify_frame_gas"]:
        raise SystemExit("VERIFY execution gas does not match the immutable dispatcher profile")
    if profile["signature_gas"] != expected["signature_gas"]:
        raise SystemExit("signature gas does not match the immutable dispatcher profile")
    if required > profile["hegota_profile_2_budget"]:
        raise SystemExit("transaction exceeds the configured Hegota Profile 2 budget")
    if profile["wire_profile"] in ("position-notes-v2", "position-notes-v3"):
        # The pre-PR 12279 figure charged keyed-nonce creation as execution gas and no
        # longer applies. The measurement on this dispatcher, native ethrex 247e2dd2,
        # must fit the default.
        if "post_pr_12279_max_observed_verify_execution_gas" not in profile:
            raise SystemExit("missing PR 12279 VERIFY execution measurement status")
        historical_verify_gas = profile["post_pr_12279_max_observed_verify_execution_gas"]
        measured_verify_gas = historical_verify_gas
    elif profile["wire_profile"] in (
            "eip8250-state-gas-pre-8272-frame", "eip8272-canonical-frame", "recipient-pull-v1",
            "position-notes-v1"):
        historical_verify_gas = profile["pre_pr_12279_max_observed_verify_execution_gas"]
        # The field is required even before a measurement exists. Its explicit
        # null records the remaining live-test gap; omitting it must not look
        # like completed evidence.
        if "post_pr_12279_max_observed_verify_execution_gas" not in profile:
            raise SystemExit("missing PR 12279 VERIFY execution measurement status")
        measured_verify_gas = profile["post_pr_12279_max_observed_verify_execution_gas"]
    else:
        historical_verify_gas = profile["max_observed_verify_gas"]
        measured_verify_gas = None
    if historical_verify_gas >= profile["verify_frame_gas"]:
        raise SystemExit("VERIFY frame does not cover the historical valid path")
    if measured_verify_gas is not None and measured_verify_gas >= profile["verify_frame_gas"]:
        raise SystemExit("VERIFY frame does not cover the PR 12279 valid path")
    if profile["settle_frame_gas"] != expected["settle_frame_gas"]:
        raise SystemExit("settlement gas does not match the immutable dispatcher profile")
    if profile["conservative_settle_bound"] >= profile["settle_frame_gas"]:
        raise SystemExit("settlement frame does not cover the conservative fork bound")
    # The state dimension is only declared by profiles that have one, and when a profile
    # has one it is mandatory: a spec-profile manifest silently missing `settle_frame_state_gas`
    # would deploy a pool whose settlement frame declares no state budget at all.
    if expected["settle_frame_state_gas"] is None:
        if "settle_frame_state_gas" in profile:
            raise SystemExit("profile declares a state budget it has no dimension for")
    else:
        if profile.get("settle_frame_state_gas") != expected["settle_frame_state_gas"]:
            raise SystemExit("settlement state gas does not match the immutable dispatcher profile")
        if profile["conservative_settle_state_bound"] >= profile["settle_frame_state_gas"]:
            raise SystemExit("settlement frame does not cover the conservative state bound")
    if expected["verify_frame_state_gas"] is None:
        if "verify_frame_state_gas" in profile:
            raise SystemExit("profile declares a VERIFY state budget it has no dimension for")
    elif profile.get("verify_frame_state_gas") != expected["verify_frame_state_gas"]:
        raise SystemExit("VERIFY state gas does not match the immutable dispatcher profile")

    # Truthiness would read the JSON string "false" as true, so require real
    # types, and take the contribution count from the pinned proving key.
    ceremony = manifest["ceremony"]
    production = manifest["production"]
    contributions = ceremony["phase2_contributions"]
    verified = ceremony["independent_verification"]
    if type(production) is not bool:
        raise SystemExit("production must be a JSON boolean")
    if type(contributions) is not int:
        raise SystemExit("phase2_contributions must be a JSON integer")
    if verified is not None and type(verified) is not bool:
        raise SystemExit("independent_verification must be a JSON boolean or null")
    if contributions != zkey_contributions(ROOT / ZKEY):
        raise SystemExit("phase2_contributions does not match the proving key")
    if not production:
        if not args.allow_testbed:
            raise SystemExit("activation blocked: manifest is testbed-only")
    elif contributions < 2 or verified is not True:
        raise SystemExit("activation blocked: production ceremony evidence is incomplete")

    # "partial": A/B terms and verifier checked, the key's points not (see check_setup).
    print(json.dumps({"artifacts": "match", "profile": "match",
                      "production": manifest["production"],
                      "setup": "verified" if args.ptau else "partial"}, sort_keys=True))


if __name__ == "__main__":
    main()
