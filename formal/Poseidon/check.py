#!/usr/bin/env python3
"""Differentially test concrete Lean Poseidon against the pinned Python reference."""

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

import generate

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node-modules", type=Path, default=ROOT / "tooling/node_modules")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    for name, expected in generate.outputs(args.node_modules).items():
        generate.require((HERE / name).read_bytes() == expected, f"regeneration mismatch: {name}")

    spec = importlib.util.spec_from_file_location("msp_poseidon_reference", ROOT / "reference/poseidon_bn254.py")
    reference = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reference)
    stored = json.loads((ROOT / "vectors/poseidon_bn254_vectors.json").read_text())
    cases = []

    def case(kind, inputs, expected=None):
        inputs = list(map(int, inputs))
        actual = reference.poseidon(inputs)
        if expected is not None:
            generate.require(actual == int(expected), f"Python disagrees with {kind} fixture")
        cases.append((kind, inputs, actual))
        return actual

    for arity in (2, 3, 10):
        for vector in stored[f"poseidon{arity}"]:
            case("committed direct vectors", vector["in"], vector["out"])

    chain = {key: int(value) for key, value in stored["pool_chain"].items()}
    owner = case("pool chain", [1, chain["spend_key"], 0], chain["owner_pk"])
    inner = case("pool chain", [owner, chain["rho"]], chain["inner"])
    cm = case("pool chain", [2, inner, chain["value"]], chain["cm"])
    key = case("pool chain", [chain["domain"], chain["spend_key"]])
    occurrence = case("pool chain", [cm, chain["index"]])
    case("pool chain", [4, key, occurrence], chain["nf"])
    dummy = case("pool chain", [2, inner, 0])
    dummy_occurrence = case("pool chain", [dummy, chain["index"]])
    case("pool chain", [4, key, dummy_occurrence], chain["nf2"])
    for k in (1, 2):
        case("pool chain", [2, chain[f"out_inner{k}"], chain[f"out_value{k}"]], chain[f"out_cm{k}"])
    for k in (1, 2):
        case("sinks", [2, k, 0])

    depth = int(stored["tree"]["depth"])
    zeros = [0]
    for _ in range(depth):
        zeros.append(case("zero chain", [zeros[-1], zeros[-1]]))
    generate.require(zeros[-1] == int(stored["tree"]["root_empty"]), "wrong empty-root vector")
    for level, expected in enumerate(zeros):
        cases.append(("recursive zero function", ["zero", level], expected))

    # Check the exact constants that C6 must eventually prove in the kernel.
    tree = (ROOT / "formal/Spec/Tree.lean").read_text()
    body = tree.split("def ZEROS : List ℕ :=", 1)[1].split("]", 1)[0]
    fixed_zeros = [int(x, 0) for x in re.findall(r"0x[0-9a-fA-F]+|\b[0-9]+\b", body)]
    empty = int(re.search(r"def EMPTY_ROOT_CONST : ℕ := (0x[0-9a-fA-F]+)", tree).group(1), 0)
    generate.require(fixed_zeros == zeros[:-1] and empty == zeros[-1], "C6 constants disagree with reference")

    filled = [0] * depth
    for index, leaf_key in enumerate(("cm0", "cm1")):
        node, position = int(stored["tree"][leaf_key]), index
        for level in range(depth):
            if position % 2 == 0:
                filled[level] = node
                node = case("incremental tree", [node, zeros[level]])
            else:
                node = case("incremental tree", [filled[level], node])
            position //= 2
        key = "root_after_cm0" if index == 0 else "root_after_cm0_cm1"
        generate.require(node == int(stored["tree"][key]), f"wrong tree vector {key}")

    rng = random.Random(20260927)
    for arity in (2, 3, 10):
        for boundary in (0, reference.P - 1, reference.P, reference.P + 1):
            case("boundary reductions", [boundary] * arity)
        for _ in range(16):
            case("additional deterministic vectors", [rng.randrange(reference.P) for _ in range(arity)])

    subprocess.run([args.lake, "build", "Poseidon"], cwd=ROOT / "formal", check=True)
    with tempfile.TemporaryDirectory(prefix="msp-poseidon-check-") as directory:
        inputs = Path(directory) / "inputs.txt"
        inputs.write_text("".join(" ".join(map(str, xs)) + "\n" for _, xs, _ in cases))
        result = subprocess.run([args.lake, "env", "lean", "--run", "Poseidon/Evaluate.lean", str(inputs)],
                                cwd=ROOT / "formal", check=True, text=True, capture_output=True)
    observed = [int(line) for line in result.stdout.splitlines()]
    generate.require(len(observed) == len(cases), "wrong number of Lean results")
    for index, ((kind, inputs, expected), actual) in enumerate(zip(cases, observed)):
        generate.require(actual == expected,
                         f"Lean mismatch at {index}, {kind}, inputs={inputs}: {actual} != {expected}")
    print(json.dumps({"result": "pass", "lean_python_comparisons": len(cases),
                      "categories": dict(Counter(kind for kind, _, _ in cases)),
                      "c6_constants_checked_by_evaluation": len(zeros),
                      "scope": "Executable tests; not a circuit-equivalence or kernel proof"}, indent=2))


if __name__ == "__main__":
    main()
