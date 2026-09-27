#!/usr/bin/env python3
"""Extract path gates and witness wires from exact pinned R1CS/symbol bytes."""
import argparse
import sys
from pathlib import Path
from r1cs_artifact import P, PIN, SYM_PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha, symbol_rows, reproduce

DESTINATION = ROOT / 'formal/Artifacts/PathBitsData.lean'


def pinned_inputs(data, sym):
    require(sha(data) == PIN, 'path/witness extraction requires exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    rows = symbol_rows(sym, artifact)
    return artifact, rows


def wire(rows, name):
    value = rows[name]['wire']
    require(value is not None, f'required witness signal is eliminated: {name}')
    return value


def vector(values):
    return '![' + ', '.join(str(value) for value in values) + ']'


def lean_constraint(constraint):
    sides = ['[' + ', '.join(f'({w}, {c})' for w, c in side) + ']' for side in constraint]
    return '⟨' + ', '.join(sides) + '⟩'


def render(data, sym):
    artifact, rows = pinned_inputs(data, sym)
    private = {field: [wire(rows, f'main.{name}[{k}]') for k in range(2)]
               for field, name in [('skWire', 'in_spend_key'), ('rhoWire', 'in_rho'),
                                   ('valueWire', 'in_value'), ('outputInnerWire', 'out_inner'),
                                   ('outputValueWire', 'out_value')]}
    siblings = [[wire(rows, f'main.in_siblings[{k}][{i}]') for i in range(20)] for k in range(2)]
    bits = [[wire(rows, f'main.in_bits[{k}][{i}]') for i in range(20)] for k in range(2)]
    starts = [path[0] for path in bits]
    require(all(path == list(range(start, start+20)) for path, start in zip(bits, starts)),
            'unexpected nonconsecutive path-bit wires')
    locations, path_constraints = [], []
    for path in bits:
        found = []
        for bit in path:
            # Match the exact retained Boolean shape in the actual artifact.
            target = [[(0, P-1), (bit, 1)], [(bit, 1)], []]
            matches = [i for i, c in enumerate(artifact['constraints']) if c == target]
            require(len(matches) == 1, f'expected one actual Boolean constraint for wire {bit}')
            found.append(matches[0])
        require(found == list(range(found[0], found[0]+20)), 'unexpected nonconsecutive path constraints')
        locations.append(found)
        path_constraints.append([artifact['constraints'][i] for i in found])
    lines = ['import Artifacts.R1CS', 'import Spec.Hash', '', '/-!', '# Exact path gates and private-wire map', '',
             f'R1CS SHA-256: `{PIN}`.', f'Reproduced symbol SHA-256: `{SYM_PIN}`.',
             'All wire indices below are extracted from that exact symbol file and',
             'checked against the R1CS wire-to-label section. Constraints are copied',
             'from the pinned binary. Semantic projections and proofs are separate.',
             '-/', '', 'namespace MSP.Artifacts.PathBitsData', '']
    for field, values in private.items():
        lines += [f'def {field} : Fin 2 → ℕ := {vector(values)}', '']
    lines += ['def siblingWire : Fin 2 → Fin DEPTH → ℕ :=',
              '  ![' + ', '.join(vector(path) for path in siblings) + ']', '',
              'def bitWires : Fin 2 → List ℕ :=',
              '  ![' + ', '.join('[' + ', '.join(str(w) for w in path) + ']' for path in bits) + ']', '',
              f'def bitStart : Fin 2 → ℕ := {vector(starts)}', '']
    for public in ('beta', 'gamma', 'alpha'):
        lines += [f'def {public}Wire : ℕ := {wire(rows, "main." + public)}', '']
    for k, constraints in enumerate(path_constraints):
        lines += [f'/-- Actual constraint indices {locations[k][0]} through {locations[k][-1]}. -/',
                  f'def path{k}Constraints : List Constraint := [']
        lines += ['  ' + lean_constraint(c) + (',' if i < 19 else '') for i, c in enumerate(constraints)]
        lines += [']', '']
    lines += ['def constraints : Fin 2 → List Constraint := ![path0Constraints, path1Constraints]', '',
              'end MSP.Artifacts.PathBitsData', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--sym', type=Path, help='exact reproduced spend.sym')
    source.add_argument('--reproduce', type=Path, metavar='NODE_MODULES', help='reproduce the exact symbols with pinned toolchain')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = (ROOT / 'build/spend.r1cs').read_bytes()
    if args.sym:
        sym = args.sym.read_bytes()
    else:
        reproduced, _, rows = reproduce(args.reproduce)
        require(reproduced == data, 'recompiled R1CS differs')
        ordered = sorted(rows.items(), key=lambda row: row[1]['label'])
        sym = ''.join(f'{row["label"]},{-1 if row["wire"] is None else row["wire"]},{row["component"]},{name}\n'
                      for name, row in ordered).encode('utf-8')
        require(sha(sym) == SYM_PIN, 'reproduced symbol serialization differs from exact pin')
    expected = render(data, sym).encode('utf-8')
    if args.write:
        DESTINATION.write_bytes(expected)
    else:
        require(DESTINATION.read_bytes() == expected, 'PathBitsData.lean differs from exact pinned extraction')
    print('PathBitsData.lean matches exact pinned path constraints and witness/public wire symbols.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
