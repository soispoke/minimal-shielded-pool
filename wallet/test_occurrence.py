"""Focused occurrence-nullifier circuit checks, using generated R1CS/WASM.

Run after compiling/setup: python3 wallet/test_occurrence.py
This exercises real witness constraints and one real Groth16 proof. It does
not emulate the protocol's consumed-key registry or authenticate epoch roots;
the native integration tests cover those boundaries separately.
"""
import copy
import json
import struct
import subprocess
import time
from pathlib import Path

import wallet as w

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
WORK = BUILD / "occurrence-tests"
RESULTS = []
STATEMENT_INPUTS = ["root", "domain", "public_amount", "fee", "recipient", "authorizer"]


def statement_for(witness, nullifiers):
    """The ten-value statement a witness should prove, given the nullifiers the
    caller expects the circuit to compute."""
    outputs = [(int(i), int(v)) for i, v in zip(witness["out_inner"], witness["out_value"])]
    out_cm1, out_cm2 = w.output_commitments(outputs)
    return w.statement(*nullifiers, out_cm1, out_cm2, *(int(witness[k]) for k in STATEMENT_INPUTS))


def run(args):
    return subprocess.run([str(x) for x in args], cwd=ROOT / "tooling",
                          capture_output=True, text=True)


def must(args):
    result = run(args)
    assert result.returncode == 0, result.stdout + result.stderr
    return result


def witness_case(name, witness, expected=True, nullifiers=None):
    start = time.monotonic()
    source = WORK / (name + ".json")
    target = WORK / (name + ".wtns")
    source.write_text(json.dumps(witness))
    result = run(["npx", "snarkjs", "wtns", "calculate",
                  BUILD / "spend_js/spend.wasm", source, target])
    assert (result.returncode == 0) == expected, name + "\n" + result.stdout + result.stderr
    publics = None
    if expected:
        must(["npx", "snarkjs", "wtns", "check", BUILD / "spend.r1cs", target])
        exported = WORK / (name + ".witness.json")
        must(["npx", "snarkjs", "wtns", "export", "json", target, exported])
        # Wire 0 is the constant; then the outputs beta and gamma, then alpha.
        beta, gamma, alpha = (int(x) for x in json.loads(exported.read_text())[1:4])
        # The statement is private. beta and gamma match the expected statement
        # only if the circuit computed exactly these ten values; this is the
        # check that binds the circuit's nullifiers to the ones passed in.
        publics = statement_for(witness, nullifiers)
        assert beta == w.compression_beta(publics), name
        assert gamma == w.fingerprint((alpha + beta) % w.P, publics), name
    RESULTS.append({"name": name, "accepted": expected,
                    "seconds": round(time.monotonic() - start, 4)})
    print("PASS", name, "accepted" if expected else "rejected", flush=True)
    return publics


def wire_names(names):
    """Wire indices of named signals, from a symbol file compiled from the same
    source as the committed R1CS."""
    sym_dir = WORK / "sym"
    sym = sym_dir / "spend.sym"
    if not sym.exists():
        sym_dir.mkdir(exist_ok=True)
        must(["npx", "circom2", ROOT / "circuits/spend.circom", "--r1cs", "--sym",
              "-l", ROOT / "tooling/node_modules", "-o", sym_dir])
        assert (sym_dir / "spend.r1cs").read_bytes() == (BUILD / "spend.r1cs").read_bytes(), \
            "symbol file does not come from the committed R1CS"
    found = {}
    for line in sym.read_text().splitlines():
        _, wire, _, name = line.split(",", 3)
        if name in names:
            found[name] = int(wire)
    return found


def patched_wtns(source, target, values):
    """Copy a .wtns file with some witness values replaced (section 2 holds the
    values, n8 bytes each, little endian)."""
    data = bytearray(source.read_bytes())
    assert data[:4] == b"wtns"
    _, sections = struct.unpack_from("<II", data, 4)
    pos, offsets = 12, {}
    for _ in range(sections):
        kind, size = struct.unpack_from("<IQ", data, pos)
        offsets[kind] = pos + 12
        pos += 12 + size
    n8 = struct.unpack_from("<I", data, offsets[1])[0]
    for index, value in values.items():
        start = offsets[2] + index * n8
        data[start:start + n8] = (value % w.P).to_bytes(n8, "little")
    target.write_bytes(data)


def constraints_bind_compression(name, statement):
    """A malicious prover cannot pick beta or gamma: forge a witness whose beta is
    not Poseidon of the statement, recompute sigma, the Horner accumulators and
    gamma to match, and require the R1CS to reject it. This fails if beta or
    gamma is ever assigned without a constraint (<-- instead of <==)."""
    wires = json.loads((WORK / (name + ".witness.json")).read_text())
    beta, gamma, alpha = (int(x) for x in wires[1:4])
    acc_names = [f"main.acc[{i}]" for i in range(10)]
    index = wire_names(["main.sigma"] + acc_names)
    forged_beta = (beta + 1) % w.P
    sigma = (alpha + forged_beta) % w.P
    acc = [0] * 10
    acc[9] = statement[9]
    for i in range(9, 0, -1):
        acc[i - 1] = (acc[i] * sigma + statement[i - 1]) % w.P
    values = {1: forged_beta, 2: acc[0]}
    if index.get("main.sigma", -1) >= 0:
        values[index["main.sigma"]] = sigma
    for i, n in enumerate(acc_names):
        if index.get(n, -1) >= 0:
            values[index[n]] = acc[i]
    for label, patch in [("forged-beta", values), ("forged-gamma", {2: gamma + 1})]:
        forged = WORK / f"{name}-{label}.wtns"
        patched_wtns(WORK / (name + ".wtns"), forged, patch)
        result = run(["npx", "snarkjs", "wtns", "check", BUILD / "spend.r1cs", forged])
        assert result.returncode != 0, (label, result.stdout)
    RESULTS.append({"name": "r1cs-rejects-forged-beta-and-gamma", "passed": True})
    print("PASS r1cs rejects a forged beta and a forged gamma", flush=True)


def main():
    WORK.mkdir(exist_ok=True)
    w.set_seed(20260921)
    pool = "0x" + "12" * 20
    domain0 = w.domain_scalar(31337, pool, 0)
    domain1 = w.domain_scalar(31337, pool, 1)
    sk, rho = w.new_note()
    real = {"sk": sk, "rho": rho, "value": 100, "idx": 0}
    cm = w.commitment(sk, rho, 100)
    tree = w.Tree()
    tree.append(cm)
    tree.append(cm)
    tree.append(w.commitment(*w.new_note(), 17))
    duplicate = dict(real, idx=1)
    dummy = w.dummy_input()
    _, authorizer = w.new_authorizer()

    def make(inputs, domain=domain0):
        return w.build_witness(tree, inputs, w.sink_outputs(), domain,
                               authorizer=authorizer,
                               public_amount=sum(n["value"] for n in inputs),
                               recipient="0x" + "34" * 20)

    first = make([real, dummy])
    second = make([duplicate, dummy])
    public_first = witness_case("first-occurrence", first,
                                nullifiers=w.input_nullifiers(domain0, [real, dummy]))
    public_second = witness_case("identical-second-occurrence", second,
                                 nullifiers=w.input_nullifiers(domain0, [duplicate, dummy]))
    assert public_first[0] != public_second[0]
    public_pair = witness_case("both-identical-funded-occurrences", make([real, duplicate]),
                               nullifiers=w.input_nullifiers(domain0, [real, duplicate]))
    assert public_pair[:2] == [public_first[0], public_second[0]]

    witness_case("same-occurrence-twice", make([real, real]), False)
    bad = make([real, duplicate])
    bad["out_inner"] = [str(w.inner(sk, rho))] * 2
    bad["out_value"] = ["100", "100"]
    bad["public_amount"] = "0"
    bad["recipient"] = "0"
    witness_case("same-output-twice-in-one-spend", bad, False)
    bad = copy.deepcopy(first)
    bad["in_bits"][0][1] = "1"  # Selects a different non-identical branch.
    witness_case("forged-real-position", bad, False)
    bad = copy.deepcopy(first)
    bad["in_bits"][0][0] = "2"
    witness_case("nonboolean-path-bit", bad, False)
    bad = copy.deepcopy(first)
    bad["root"] = str((int(first["root"]) + 1) % w.P)
    witness_case("incorrect-root", bad, False)

    # The same input epoch, commitment and position retain their spending
    # identity when the root changes. Publication slot is intentionally absent.
    tree.append(w.commitment(*w.new_note(), 29))
    later = make([real, dummy])
    public_later = witness_case("same-occurrence-later-root", later,
                                nullifiers=w.input_nullifiers(domain0, [real, dummy]))
    assert public_later[4] != public_first[4]
    assert public_later[:2] == public_first[:2]

    # Both epochs have to be authenticated independently by the dispatcher.
    # This circuit test only checks domain separation, not root provenance.
    other_epoch = make([real, dummy], domain1)
    public_epoch = witness_case("same-position-other-authenticated-epoch", other_epoch,
                                nullifiers=w.input_nullifiers(domain1, [real, dummy]))
    assert public_epoch[0] != public_later[0]

    # A reorg can change the insertion order. Reconstruct the canonical tree
    # and input index before reproving; retaining the old path must fail.
    branch_a = w.Tree()
    other_cm = w.commitment(*w.new_note(), 37)
    branch_a.append(cm)
    branch_a.append(other_cm)
    branch_b = w.Tree()
    branch_b.append(other_cm)
    branch_b.append(cm)
    original = w.build_witness(branch_a, [real, dummy], w.sink_outputs(), domain0,
                               authorizer=authorizer, public_amount=100,
                               recipient="0x" + "34" * 20)
    stale = copy.deepcopy(original)
    stale["root"] = str(branch_b.root())
    witness_case("reorg-stale-membership-path", stale, False)
    rebuilt_input = dict(real, idx=1)
    rebuilt = w.build_witness(branch_b, [rebuilt_input, dummy], w.sink_outputs(), domain0,
                              authorizer=authorizer, public_amount=100,
                              recipient="0x" + "34" * 20)
    public_rebuilt = witness_case("reorg-rebuilt-tree-and-index", rebuilt,
                                  nullifiers=w.input_nullifiers(domain0, [rebuilt_input, dummy]))
    assert public_rebuilt[0] != public_first[0]

    # Each witness below breaks exactly one constraint, so deleting or weakening
    # that constraint alone would let it through.
    bad = copy.deepcopy(first)
    bad["public_amount"] = "101"
    witness_case("outputs-exceed-inputs", bad, False)
    bad["public_amount"] = "99"
    witness_case("inputs-exceed-outputs", bad, False)
    bad = copy.deepcopy(first)
    bad["public_amount"], bad["fee"] = "101", str(w.P - 1)  # conserved mod p only
    witness_case("value-wraps-the-field", bad, False)
    # A dummy's membership is gated off by its zero value, so a non-boolean
    # path bit there breaks only the booleanity constraint, at any depth.
    for depth in (0, 10, 19):
        bad = copy.deepcopy(first)
        bad["in_bits"][1][depth] = "2"
        witness_case(f"nonboolean-dummy-path-bit-{depth}", bad, False)
    transfer = w.build_witness(tree, [real, dummy], [(w.inner(*w.new_note()), 60), (w.inner(*w.new_note()), 40)],
                               domain0, authorizer=authorizer, public_amount=0)
    for position in (0, 1):
        bad = copy.deepcopy(transfer)
        bad["out_value"] = ["0", "100"] if position == 0 else ["100", "0"]
        witness_case(f"zero-output-{position}-without-its-sink", bad, False)
    bad = copy.deepcopy(transfer)
    bad["out_inner"][0] = "2"
    witness_case("positive-output-with-the-second-sink", bad, False)

    same_secrets_dummy = {"sk": sk, "rho": rho, "value": 0, "idx": None}
    public_dummy = witness_case("dummy-same-secret-and-position", make([real, same_secrets_dummy]),
                                nullifiers=w.input_nullifiers(domain0, [real, same_secrets_dummy]))
    assert public_dummy[0] != public_dummy[1]
    dummy_at_max = make([real, same_secrets_dummy])
    dummy_at_max["in_bits"][1] = ["1"] * w.DEPTH
    max_dummy_nf = w.nullifier(domain0, sk, w.commitment(sk, rho, 0), (1 << w.DEPTH) - 1)
    public_dummy_max = witness_case("dummy-arbitrary-maximum-position", dummy_at_max,
                                    nullifiers=[public_dummy[0], max_dummy_nf])
    assert public_dummy_max[1] != public_later[0]

    # Epoch and index range checks in the reference helper must agree with
    # canonical dispatcher uint64 epochs and depth-20 path indices.
    for invalid_epoch in [-1, 1 << 64]:
        try:
            w.domain_scalar(31337, pool, invalid_epoch)
            raise AssertionError("accepted invalid epoch")
        except ValueError:
            pass
    for invalid_index in [-1, 1 << w.DEPTH]:
        try:
            w.nullifier(domain0, sk, cm, invalid_index)
            raise AssertionError("accepted invalid index")
        except ValueError:
            pass
    RESULTS.append({"name": "reference-canonical-epoch-and-index-bounds", "passed": True})

    constraints_bind_compression("first-occurrence", public_first)

    proof = WORK / "proof.json"
    publics = WORK / "public.json"
    start = time.monotonic()
    must(["npx", "snarkjs", "groth16", "prove", BUILD / "spend_final.zkey",
          WORK / "first-occurrence.wtns", proof, publics])
    prove_seconds = time.monotonic() - start
    key = ROOT / "contracts/vectors/spend_vkey.json"
    must(["npx", "snarkjs", "groth16", "verify", key, publics, proof])
    RESULTS.append({"name": "real-groth16-proof", "passed": True,
                    "prove_seconds": round(prove_seconds, 4)})
    # The verifier sees (beta, gamma, alpha). Recompute alpha and gamma as the
    # pool would for a statement with one value changed; the proof must fail.
    beta, gamma, alpha = (int(x) for x in json.loads(publics.read_text()))
    assert alpha == w.compression_alpha(public_first), "alpha does not hash the statement"
    assert gamma == w.fingerprint((alpha + beta) % w.P, public_first)
    mutated_path = WORK / "mutated-public.json"

    def rejects(signals, label):
        mutated_path.write_text(json.dumps([str(x) for x in signals]))
        rejected = run(["npx", "snarkjs", "groth16", "verify", key, mutated_path, proof])
        assert rejected.returncode != 0 or "Invalid proof" in rejected.stdout, (label, rejected.stdout)

    for index in range(10):
        stmt = list(public_first)
        stmt[index] = domain1 if index == 5 else (stmt[index] + 1) % w.P
        mutated_alpha = w.compression_alpha(stmt)
        rejects([beta, w.fingerprint((mutated_alpha + beta) % w.P, stmt), mutated_alpha],
                f"statement[{index}]")
    RESULTS.append({"name": "proof-rejects-each-mutated-statement-value", "passed": True})
    rejects([(beta + 1) % w.P, gamma, alpha], "beta")
    rejects([beta, (gamma + 1) % w.P, alpha], "gamma")
    RESULTS.append({"name": "proof-rejects-mutated-beta-and-gamma", "passed": True})
    (WORK / "report.json").write_text(json.dumps({"cases": RESULTS}, indent=2) + "\n")
    print(f"PASS {len(RESULTS)} focused circuit/reference/proof cases", flush=True)


if __name__ == "__main__":
    main()
