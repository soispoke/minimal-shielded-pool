#!/usr/bin/env python3
"""Extract the first actual 128-bit gate, including its eliminated top bit."""
import argparse
import sys
from pathlib import Path
from r1cs_artifact import PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha, symbol_rows

START = 13870
COUNT = 128
WIRE_START = 13918
DESTINATION = ROOT / 'formal/Artifacts/RangeData.lean'


def render(data):
    require(sha(data) == PIN, 'range fragment requires exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    lines = ['import Artifacts.R1CS', '', '/-!', '# Exact first input range constraints', '',
             f'Generated from SHA-256 `{PIN}`, constraints 13870 through 13997.',
             'These constrain input wire 10 through 127 retained bit wires and an',
             'eliminated top bit. Interpretation is proved separately in Range.lean.',
             'Regenerate with `python3 formal/tools/range_fragment.py --write`.',
             '-/', '', 'namespace MSP.Artifacts.RangeData', '',
             'set_option maxRecDepth 4096', '', 'def lowConstraints : List Constraint := [']
    constraints = artifact['constraints'][START:START + COUNT]
    for index, constraint in enumerate(constraints[:127]):
        sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
                 for side in constraint]
        lines.append('  ⟨' + ', '.join(sides) + '⟩' + (',' if index < 126 else ''))
    lines += [']', '', 'def topConstraint : Constraint :=']
    sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
             for side in constraints[127]]
    lines += ['  ⟨' + ', '.join(sides) + '⟩', '',
              'def constraints : List Constraint := lowConstraints ++ [topConstraint]', '',
              'end MSP.Artifacts.RangeData', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--sym', type=Path, help='also check the exact reproduced symbol map')
    args = parser.parse_args()
    data = (ROOT / 'build/spend.r1cs').read_bytes()
    expected = render(data).encode('utf-8')
    if args.sym:
        rows = symbol_rows(args.sym.read_bytes(), parse_r1cs(data, pinned_compat=True))
        require(rows['main.in_value[0]']['wire'] == 10, 'wrong first input wire')
        for i in range(127):
            require(rows[f'main.spend.rc[0].out[{i}]']['wire'] == WIRE_START + i, 'wrong retained bit wire')
        require(rows['main.spend.rc[0].out[127]']['wire'] is None, 'top bit was not eliminated')
    if args.write:
        DESTINATION.write_bytes(expected)
    else:
        require(DESTINATION.read_bytes() == expected, 'RangeData.lean differs from exact pinned range constraints')
    print('RangeData.lean matches exact constraints 13870..13997; five other amount gates remain open.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
