#!/usr/bin/env python3
"""Extract the two exact 160-bit address gates from the pinned R1CS."""
import argparse
import sys
from pathlib import Path
from r1cs_artifact import PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha, symbol_rows

GATES = (
    ('recipient', 14638, 14680, 'main.spend.recipientBits', 97),
    ('authorizer', 474, 569, 'main.spend.authorizerBits', 98),
)
DESTINATION = ROOT / 'formal/Artifacts/RangeAddressData.lean'


def lean_constraint(constraint):
    sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
             for side in constraint]
    return '⟨' + ', '.join(sides) + '⟩'


def render(data):
    require(sha(data) == PIN, 'address range fragments require exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    lines = ['import Artifacts.R1CS', '', '/-!', '# Exact address range constraints', '',
             f'Generated from SHA-256 `{PIN}`.',
             'Each gate contains 159 retained Boolean bit wires and an eliminated',
             'top bit. Interpretation and full-system membership are proved separately.',
             'Regenerate with `python3 formal/tools/range_address_fragment.py --write`.',
             '-/', '', 'namespace MSP.Artifacts.RangeAddressData', '',
             'set_option maxRecDepth 4096', '']
    for name, start, _, _, _ in GATES:
        constraints = artifact['constraints'][start:start + 160]
        lines += [f'/-- Constraint indices {start} through {start + 158}. -/',
                  f'def {name}Low : List Constraint := [']
        lines += ['  ' + lean_constraint(constraint) + (',' if i < 158 else '')
                  for i, constraint in enumerate(constraints[:159])]
        lines += [']', '', f'/-- Constraint index {start + 159}: the actual eliminated top-bit gate. -/',
                  f'def {name}Top : Constraint :=', '  ' + lean_constraint(constraints[159]), '',
                  f'def {name}Constraints : List Constraint := {name}Low ++ [{name}Top]', '']
    lines += ['end MSP.Artifacts.RangeAddressData', '']
    return '\n'.join(lines)


def check_symbols(sym, data):
    rows = symbol_rows(sym, parse_r1cs(data, pinned_compat=True))
    for name, _, wire_start, component, address_wire in GATES:
        require(rows[f'main.{name}']['wire'] == address_wire, f'wrong {name} address wire')
        for i in range(159):
            require(rows[f'{component}.out[{i}]']['wire'] == wire_start + i,
                    f'wrong retained {name} bit wire')
        require(rows[f'{component}.out[159]']['wire'] is None, f'{name} top bit was not eliminated')


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
        require(DESTINATION.read_bytes() == expected, 'RangeAddressData.lean differs from exact pinned constraints')
    print('RangeAddressData.lean matches exact pinned recipient and authorizer 160-bit gates.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
