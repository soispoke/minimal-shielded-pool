#!/usr/bin/env python3
"""Extract the other five actual 128-bit amount gates from the pinned R1CS."""
import argparse
import sys
from pathlib import Path
from r1cs_artifact import PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha, symbol_rows

GATES = (
    ('secondInput', 13998, 14045, 'main.in_value[1]', 11),
    ('firstOutput', 14126, 14172, 'main.out_value[0]', 94),
    ('secondOutput', 14254, 14299, 'main.out_value[1]', 95),
    ('publicAmount', 14382, 14426, 'main.public_amount', 96),
    ('fee', 14510, 14553, 'main.fee', None),
)
DESTINATION = ROOT / 'formal/Artifacts/RangeAmountsData.lean'


def lean_constraint(constraint):
    sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
             for side in constraint]
    return '⟨' + ', '.join(sides) + '⟩'


def render(data):
    require(sha(data) == PIN, 'amount range fragments require exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    lines = ['import Artifacts.R1CS', '', '/-!', '# Exact remaining amount range constraints', '',
             f'Generated from SHA-256 `{PIN}`.',
             'Constraints 13998..14637 contain the second input, two outputs,',
             'public amount and fee gates. Each has an eliminated top bit.',
             'Regenerate with `python3 formal/tools/range_amounts.py --write`.',
             '-/', '', 'namespace MSP.Artifacts.RangeAmountsData', '',
             'set_option maxRecDepth 4096', '']
    for name, start, _, _, _ in GATES:
        constraints = artifact['constraints'][start:start + 128]
        lines += [f'/-- Constraint indices {start} through {start + 126}. -/',
                  f'def {name}Low : List Constraint := [']
        lines += ['  ' + lean_constraint(constraint) + (',' if i < 126 else '')
                  for i, constraint in enumerate(constraints[:127])]
        lines += [']', '', f'/-- Constraint index {start + 127}, including the actual top-bit linear combination. -/',
                  f'def {name}Top : Constraint :=', '  ' + lean_constraint(constraints[127]), '',
                  f'def {name}Constraints : List Constraint := {name}Low ++ [{name}Top]', '']
    lines += ['end MSP.Artifacts.RangeAmountsData', '']
    return '\n'.join(lines)


def check_symbols(sym, data):
    rows = symbol_rows(sym, parse_r1cs(data, pinned_compat=True))
    for gate, (_, _, wire_start, amount, wire) in enumerate(GATES, 1):
        require(rows[amount]['wire'] == wire, f'wrong amount wire for gate {gate}')
        for i in range(127):
            require(rows[f'main.spend.rc[{gate}].out[{i}]']['wire'] == wire_start + i,
                    f'wrong retained bit wire for gate {gate}')
        require(rows[f'main.spend.rc[{gate}].out[127]']['wire'] is None,
                f'top bit was not eliminated in gate {gate}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--sym', type=Path, help='also check the exact reproduced symbol map')
    args = parser.parse_args()
    data = (ROOT / 'build/spend.r1cs').read_bytes()
    expected = render(data).encode('utf-8')
    if args.sym:
        check_symbols(args.sym.read_bytes(), data)
    if args.write:
        DESTINATION.write_bytes(expected)
    else:
        require(DESTINATION.read_bytes() == expected, 'RangeAmountsData.lean differs from exact pinned constraints')
    print('RangeAmountsData.lean matches exact pinned constraints 13998..14637, including the eliminated fee.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
