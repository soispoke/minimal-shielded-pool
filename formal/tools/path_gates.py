#!/usr/bin/env python3
"""Extract exact pinned Merkle selectors and gated-root constraints."""
import argparse
import sys
from pathlib import Path
from path_bits_fragment import pinned_inputs, wire, vector, lean_constraint
from r1cs_artifact import P, PIN, SYM_PIN, ROOT, InvalidArtifact, require, reproduce, sha

DESTINATION = ROOT / 'formal/Artifacts/PathGatesData.lean'
LOCATIONS = [(656, 696), (7008, 7048)]


def extract(data, sym):
    artifact, rows = pinned_inputs(data, sym)
    starts = {}
    for field, count in [('cur', 21), ('left', 20), ('right', 20)]:
        paths = [[wire(rows, f'main.spend.note[{k}].{field}[{i}]') for i in range(count)]
                 for k in range(2)]
        starts[field] = [path[0] for path in paths]
        require(all(path == list(range(path[0], path[0]+count)) for path in paths),
                f'{field} wires are not consecutive')
    fragments = []
    for k, (start, end) in enumerate(LOCATIONS):
        constraints = artifact['constraints'][start:end+1]
        for i in range(20):
            cur, left, right = [starts[f][k]+i for f in ['cur', 'left', 'right']]
            bit = wire(rows, f'main.in_bits[{k}][{i}]')
            sibling = wire(rows, f'main.in_siblings[{k}][{i}]')
            expected = [
                [[(cur, 1), (sibling, P-1)], [(bit, 1)], [(cur, 1), (left, P-1)]],
                [[(cur, P-1), (sibling, 1)], [(bit, 1)], [(sibling, 1), (right, P-1)]]]
            for j in range(2):
                require(all(sorted(a) == sorted(b) for a, b in zip(constraints[2*i+j], expected[j])),
                        f'wrong selector equation at {start+2*i+j}')
        root = wire(rows, 'main.root')
        value = wire(rows, f'main.in_value[{k}]')
        expected = [[(root, P-1), (starts['cur'][k]+20, 1)], [(value, 1)], []]
        require(constraints[40] == expected, f'wrong gated-root constraint at {end}')
        fragments.append(constraints)
    return starts, fragments


def render(data, sym):
    starts, fragments = extract(data, sym)
    lines = ['import Artifacts.R1CS', 'import Spec.Hash', '', '/-!',
             '# Exact Merkle selector and membership gates', '',
             f'R1CS SHA-256: `{PIN}`.', f'Symbol SHA-256: `{SYM_PIN}`.',
             'Retained cur/left/right wires are extracted from the pinned symbols.',
             'Constraints 656..696 and 7008..7048 are copied with original term order.',
             'Leaf and node hash semantics are deliberately not part of this data.',
             '-/', '', 'namespace MSP.Artifacts.PathGatesData', '']
    for field in ['cur', 'left', 'right']:
        lines += [f'def {field}Start : Fin 2 → ℕ := {vector(starts[field])}', '']
    for k, constraints in enumerate(fragments):
        lines += [f'def path{k}Constraints : List Constraint := [']
        lines += ['  '+lean_constraint(c)+(',' if i<40 else '') for i,c in enumerate(constraints)]
        lines += [']', '']
    lines += ['def constraints : Fin 2 → List Constraint := ![path0Constraints, path1Constraints]', '']
    for side, offset in [('left', 0), ('right', 1)]:
        values = [vector([lean_constraint(c[2*i+offset]) for i in range(20)]) for c in fragments]
        lines += [f'def {side}Constraint : Fin 2 → Fin DEPTH → Constraint :=', '  '+vector(values), '']
    lines += ['def rootConstraint : Fin 2 → Constraint :=',
              '  '+vector([lean_constraint(c[40]) for c in fragments]), '',
              'end MSP.Artifacts.PathGatesData', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--sym', type=Path, help='exact reproduced spend.sym')
    source.add_argument('--reproduce', type=Path, metavar='NODE_MODULES',
                        help='reproduce the symbols with the pinned compiler')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = (ROOT/'build/spend.r1cs').read_bytes()
    if args.sym:
        sym = args.sym.read_bytes()
    else:
        reproduced, _, rows = reproduce(args.reproduce)
        require(reproduced == data, 'recompiled R1CS differs')
        ordered = sorted(rows.items(), key=lambda row: row[1]['label'])
        sym = ''.join(f'{row["label"]},{-1 if row["wire"] is None else row["wire"]},{row["component"]},{name}\n'
                      for name, row in ordered).encode('utf-8')
        require(sha(sym) == SYM_PIN, 'reproduced symbol serialization differs from exact pin')
    expected = render(data, sym).encode()
    if args.write:
        DESTINATION.write_bytes(expected)
    else:
        require(DESTINATION.read_bytes() == expected, 'PathGatesData.lean differs from pinned extraction')
    print('PathGatesData.lean matches all 80 selectors, two root gates, and exact symbol wires.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
