#!/usr/bin/env python3
"""Differentially test the executable Lean model (formal/Spec) against wallet/wallet.py.

The script draws seeded random inputs, appends one `#eval` per case to a copy of
`DifferentialModel.lean`, runs it with `lake env lean`, and compares every
printed value with the wallet's computation of the same quantity. It exits
nonzero on any mismatch, any missing value, or a Lean failure.

What is evaluated where (see the Lean driver's header):

* Directly from `Spec`: pk, inner, cm, D, DOMAIN_TAG, nfKey, nf, SINK, Z,
  EMPTY_ROOT, zeroConst, EMPTY_ROOT_CONST, MR, alpha, beta, gamma,
  LogicTree.insert/root, treeRoot at heights 1..6, and siblingsOf at levels
  below --direct-levels.
* Through copies proved equal in the driver (`treeRootFast_eq`, `TRFast_eq`,
  `siblingsOfFast_eq`, `mkSpendFast_eq`): TR at depth 20, siblingsOf at every
  level, and mkSpend. `--direct-spend K` also evaluates `Spec`'s own mkSpend
  (hence TR and siblingsOf at depth 20) on the first K spend inputs; each case
  costs about 3 * 2^20 interpreted Poseidon calls.

This is an executable test, not a proof.
"""
import argparse
import hashlib
import json
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parent
ROOT = FORMAL.parent
DRIVER = HERE / "DifferentialModel.lean"

sys.path.insert(0, str(ROOT / "wallet"))
import wallet as W  # noqa: E402  (inserts ../reference on sys.path itself)
from poseidon_bn254 import P, p2  # noqa: E402

DEPTH = 20
U128 = 1 << 128


# ---- case generation ----

def generate(seed, n, direct_spend=0):
    """Seeded cases: a list of (kind, cid, args) with plain-integer arguments."""
    rng = random.Random(seed)
    fe = lambda: rng.randrange(P)  # noqa: E731
    cases = [("const", "const", {})]

    note_bounds = [(0, 0, 0, 0, 0), (P - 1, P - 1, U128 - 1, P - 1, (1 << DEPTH) - 1),
                   (1, 2, 1, 0, 1)]
    for k in range(n):
        if k < len(note_bounds):
            sk, rho, v, d, i = note_bounds[k]
        else:
            sk, rho, d = fe(), fe(), fe()
            v = rng.randrange(U128) if k % 4 else fe()
            i = rng.randrange(1 << DEPTH)
        cases.append(("note", f"note/{k}", dict(sk=sk, rho=rho, v=v, d=d, i=i)))

    for k in range(n):
        inr, v = (fe(), rng.randrange(U128)) if k else (P - 1, U128 - 1)
        cases.append(("cm", f"cm/{k}", dict(inr=inr, v=v)))

    dom_bounds = [(0, 0, 0), ((1 << 256) - 1, (1 << 160) - 1, (1 << 64) - 1), (1, 1, 1),
                  (11155111, rng.randrange(1 << 160), 0)]
    for k in range(n):
        if k < len(dom_bounds):
            c, a, e = dom_bounds[k]
        else:
            c = rng.randrange(1 << 256) if k % 2 else rng.randrange(1 << 32)
            a, e = rng.randrange(1 << 160), rng.randrange(1 << 64)
        cases.append(("domain", f"domain/{k}", dict(c=c, a=a, e=e)))

    for k in range(n):
        h = 1 + k % 6
        size = [0, 1 << h, (1 << h) - 1][k % 3] if k < 18 else rng.randint(0, 1 << h)
        leaves = [fe() if rng.random() < 0.9 else 0 for _ in range(size)]
        cases.append(("smalltree", f"smalltree/{k}", dict(h=h, L=leaves)))

    for k in range(n):
        size = [0, 1, 2, 3, 32, 33][k] if k < 6 else rng.randint(0, 40)
        leaves = [fe() if rng.random() < 0.9 else 0 for _ in range(size)]
        if size and k % 5:
            i = rng.randrange(size)
        elif k == 5:
            i = (1 << DEPTH) - 1
        else:
            i = rng.randrange(1 << DEPTH)
        cases.append(("tree", f"tree/{k}", dict(L=leaves, i=i)))

    stmt_bounds = [[0] * 10, [P - 1] * 10, list(range(10))]
    for k in range(n):
        xs = stmt_bounds[k] if k < len(stmt_bounds) else [fe() for _ in range(10)]
        s = [0, P - 1, 1][k] if k < 3 else fe()
        cases.append(("compression", f"compression/{k}", dict(xs=xs, s=s)))

    spends = []
    for k in range(n):
        size = rng.randint(1, 24)
        i = rng.randrange(size)
        sk, rho = fe(), fe()
        v = [1, U128 - 1][k] if k < 2 else rng.randrange(1, U128)
        leaves = [fe() for _ in range(size)]
        leaves[i] = W.commitment(sk, rho, v)
        f = [0, v - 1][k % 2] if k < 4 else rng.randrange(v)
        args = dict(c=rng.randrange(1 << 256), A=rng.randrange(1, 1 << 160),
                    e=rng.randrange(1 << 64), L=leaves, i=i, sk=sk, rho=rho, v=v,
                    skd=fe(), rhod=fe(), f=f, rcp=rng.randrange(1, 1 << 160),
                    auth=rng.randrange(1, 1 << 160), s=fe())
        spends.append(args)
        cases.append(("spend", f"spend/{k}", args))
    for k in range(direct_spend):
        cases.append(("spenddirect", f"spenddirect/{k}", spends[k]))
    return cases


# ---- the Lean side ----

def lean_list(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def lean_line(kind, cid, a, direct_levels):
    q = f'"{cid}"'
    if kind == "const":
        return "#eval constCase"
    if kind == "note":
        return f"#eval noteCase {q} {a['sk']} {a['rho']} {a['v']} {a['d']} {a['i']}"
    if kind == "cm":
        return f"#eval cmCase {q} {a['inr']} {a['v']}"
    if kind == "domain":
        return f"#eval domainCase {q} {a['c']} {a['a']} {a['e']}"
    if kind == "smalltree":
        return f"#eval smallTreeCase {q} {a['h']} {lean_list(a['L'])}"
    if kind == "tree":
        sibs, _ = wallet_tree(a["L"]).auth_path(a["i"])
        return f"#eval treeCase {q} {lean_list(a['L'])} {a['i']} {lean_list(sibs)} {direct_levels}"
    if kind == "compression":
        return f"#eval compressionCase {q} {lean_list(a['xs'])} {a['s']}"
    if kind in ("spend", "spenddirect"):
        fn = "spendCase" if kind == "spend" else "spendDirectCase"
        return (f"#eval {fn} {q} {a['c']} {a['A']} {a['e']} {lean_list(a['L'])} {a['i']} "
                f"{a['sk']} {a['rho']} {a['v']} {a['skd']} {a['rhod']} {a['f']} {a['rcp']} "
                f"{a['auth']} {a['s']}")
    raise ValueError(kind)


def lean_source(cases, direct_levels):
    lines = [lean_line(kind, cid, a, direct_levels) for kind, cid, a in cases]
    return DRIVER.read_text() + "\n" + "\n".join(lines) + "\n"


def parse_lean_output(text):
    """Map (case, field) to an integer from lines `R <case> <field> <decimal>`."""
    observed = {}
    for line in text.splitlines():
        if not line.startswith("R "):
            continue
        parts = line.split()
        if len(parts) != 4 or not parts[3].isdigit():
            raise ValueError(f"malformed Lean result line: {line!r}")
        key = (parts[1], parts[2])
        if key in observed:
            raise ValueError(f"duplicate Lean result: {key}")
        observed[key] = int(parts[3])
    return observed


def run_lean(source, lake="lake", keep=None):
    with tempfile.TemporaryDirectory(prefix="msp-differential-") as directory:
        path = Path(keep) if keep else Path(directory) / "DifferentialModelRun.lean"
        path.write_text(source)
        start = time.monotonic()
        result = subprocess.run([lake, "env", "lean", str(path)], cwd=FORMAL,
                                text=True, capture_output=True)
        elapsed = time.monotonic() - start
    other = [line for line in (result.stdout + result.stderr).splitlines()
             if line.strip() and not line.startswith("R ")]
    # A clean run prints only result lines; any message, including a warning
    # that a driver lemma uses `sorry`, fails the run.
    if result.returncode != 0 or other:
        raise RuntimeError("Lean run failed or printed messages:\n" + "\n".join(other[:40]))
    return parse_lean_output(result.stdout), elapsed, other


# ---- the wallet side ----

def wallet_tree(leaves, depth=DEPTH):
    t = W.Tree(depth)
    for leaf in leaves:
        t.append(leaf)
    return t


def expect_spend(a):
    """The wallet's canonical spend for mkSpend's inputs: the real input, a
    dummy, both positional sinks, `v - f` withdrawn to `rcp`."""
    tree = wallet_tree(a["L"])
    domain = W.domain_scalar(a["c"], a["A"], a["e"])
    inputs = [{"sk": a["sk"], "rho": a["rho"], "value": a["v"], "idx": a["i"]},
              {"sk": a["skd"], "rho": a["rhod"], "value": 0, "idx": None}]
    outputs = W.sink_outputs()
    wit = W.build_witness(tree, inputs, outputs, domain, authorizer=a["auth"],
                          public_amount=a["v"] - a["f"], fee=a["f"],
                          recipient="0x%040x" % a["rcp"])
    nf1, nf2 = W.input_nullifiers(domain, inputs)
    o1, o2 = W.output_commitments(outputs)
    stmt = W.statement(nf1, nf2, o1, o2, int(wit["root"]), int(wit["domain"]),
                       int(wit["public_amount"]), int(wit["fee"]), int(wit["recipient"]),
                       int(wit["authorizer"]))
    e = {f"x{j}": x for j, x in enumerate(stmt)}
    e.update(alpha=int(wit["alpha"]), beta=W.compression_beta(stmt),
             gamma=W.fingerprint(a["s"], stmt))
    for k in range(2):
        e[f"sk{k}"] = int(wit["in_spend_key"][k])
        e[f"rho{k}"] = int(wit["in_rho"][k])
        e[f"v{k}"] = int(wit["in_value"][k])
        e[f"idx{k}"] = sum(int(b) << l for l, b in enumerate(wit["in_bits"][k]))
        e[f"oi{k}"] = int(wit["out_inner"][k])
        e[f"ov{k}"] = int(wit["out_value"][k])
        e[f"leaf{k}"] = W.commitment(inputs[k]["sk"], inputs[k]["rho"], inputs[k]["value"])
        for l in range(DEPTH):
            e[f"sib{k}_{l}"] = int(wit["in_siblings"][k][l])
    return e


def expectations(cases, direct_levels):
    """Map (case, field) to the wallet's value."""
    expected = {}
    for kind, cid, a in cases:
        if kind == "const":
            zeros = W.Tree().zeros
            e = {"DOMAIN_TAG": int.from_bytes(W.DOMAIN_TAG, "big"),
                 "SINK0": W.sink_commitments()[0], "SINK1": W.sink_commitments()[1],
                 "EMPTY_ROOT": W.Tree().root(), "EMPTY_ROOT_CONST": zeros[DEPTH]}
            e.update({f"Z{l}": zeros[l] for l in range(DEPTH + 1)})
            e.update({f"zeroConst{l}": zeros[l] for l in range(DEPTH)})
        elif kind == "note":
            leaf = W.commitment(a["sk"], a["rho"], a["v"])
            # The wallet has no separate nullifier-key function: `nullifier`
            # hashes p2(domain, spend_key) inline, so nfKey uses that block.
            e = {"pk": W.owner_pk(a["sk"]), "inner": W.inner(a["sk"], a["rho"]), "cm": leaf,
                 "nfKey": p2(a["d"], a["sk"]),
                 "nf": W.nullifier(a["d"], a["sk"], leaf, a["i"])}
        elif kind == "cm":
            e = {"cm": W.output_commitments([(a["inr"], a["v"])])[0]}
        elif kind == "domain":
            e = {"D": W.domain_scalar(a["c"], a["a"], a["e"])}
        elif kind == "smalltree":
            e = {"treeRoot": wallet_tree(a["L"], a["h"]).root()}
        elif kind == "tree":
            t = wallet_tree(a["L"])
            root = t.root()
            sibs, bits = t.auth_path(a["i"])
            e = {"TR": root, "MRwallet": root, "MRmodel": root, "logicRoot": root}
            for l in range(DEPTH):
                e[f"sib{l}"] = sibs[l]
                e[f"bit{l}"] = bits[l]
                if l < direct_levels:
                    e[f"sibDirect{l}"] = sibs[l]
        elif kind == "compression":
            xs = a["xs"]
            e = {f"x{j}": x for j, x in enumerate(xs)}
            e.update(alpha=W.compression_alpha(xs), beta=W.compression_beta(xs),
                     gamma=W.fingerprint(a["s"], xs))
        elif kind in ("spend", "spenddirect"):
            e = expect_spend(a)
        else:
            raise ValueError(kind)
        expected.update({(cid, field): value for field, value in e.items()})
    return expected


def compare(expected, observed):
    """Mismatched and missing (case, field) keys, with both values."""
    problems = []
    for key, want in expected.items():
        got = observed.get(key)
        if got is None:
            problems.append({"case": key[0], "field": key[1], "wallet": str(want), "lean": None})
        elif got != want:
            problems.append({"case": key[0], "field": key[1], "wallet": str(want), "lean": str(got)})
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--seed", type=int, default=20260927)
    parser.add_argument("-n", "--cases", type=int, default=100, help="cases per category")
    parser.add_argument("--direct-levels", type=int, default=8,
                        help="siblingsOf levels also evaluated straight from Spec")
    parser.add_argument("--direct-spend", type=int, default=0,
                        help="spend inputs also evaluated through Spec's mkSpend (slow)")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--keep-lean", help="also write the generated Lean file here")
    args = parser.parse_args(argv)
    if args.direct_spend > args.cases:
        parser.error("--direct-spend exceeds --cases")

    start = time.monotonic()
    cases = generate(args.seed, args.cases, args.direct_spend)
    source = lean_source(cases, args.direct_levels)
    expected = expectations(cases, args.direct_levels)
    observed, lean_seconds, notes = run_lean(source, args.lake, args.keep_lean)
    problems = compare(expected, observed)
    kind_of = {cid: kind for kind, cid, _ in cases}
    by_kind = {}
    for kind, cid, _ in cases:
        by_kind.setdefault(kind, [0, 0])
        by_kind[kind][0] += 1
    for cid, _ in expected:
        by_kind[kind_of[cid]][1] += 1
    inputs = {cid: a for _, cid, a in cases}
    for problem in problems:
        problem["inputs"] = {k: (str(v) if isinstance(v, int) else [str(x) for x in v])
                             for k, v in inputs[problem["case"]].items()}
    summary = {
        "result": "pass" if not problems else "FAIL",
        "seed": args.seed,
        "cases_per_category": args.cases,
        "direct_siblings_levels": args.direct_levels,
        "direct_mkSpend_cases": args.direct_spend,
        "cases_and_comparisons_by_kind": {k: {"cases": c, "comparisons": m}
                                          for k, (c, m) in by_kind.items()},
        "total_cases": len(cases),
        "total_comparisons": len(expected),
        "unexpected_lean_values": len(set(observed) - set(expected)),
        "problems": problems[:50],
        "problem_count": len(problems),
        "lean_messages": notes[:20],
        "generated_lean_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "driver_sha256": hashlib.sha256(DRIVER.read_bytes()).hexdigest(),
        "lean_seconds": round(lean_seconds, 1),
        "total_seconds": round(time.monotonic() - start, 1),
        "scope": "Executable differential test of Spec definitions against wallet.py; not a proof",
    }
    print(json.dumps(summary, indent=2))
    return 0 if not problems else 1


if __name__ == "__main__":
    sys.exit(main())
