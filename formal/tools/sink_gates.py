#!/usr/bin/env python3
"""Extract the actual output sink gates from the pinned spend R1CS."""
import argparse
import sys
from pathlib import Path
from r1cs_artifact import PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha, symbol_rows

CONTROLS = range(468, 474)
GADGETS = range(13856, 13868)
DESTINATION = ROOT / 'formal/Artifacts/SinkGatesData.lean'


def render(data):
    require(sha(data) == PIN, 'sink gates require exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    lines = ['import Artifacts.R1CS', '', '/-!', '# Exact output sink constraints', '',
             f'Generated from SHA-256 `{PIN}`.',
             'Constraints 468..473 control the sinks; 13856..13867 are their IsZero/IsEqual gates.',
             'Regenerate with `python3 formal/tools/sink_gates.py --write`.',
             '-/', '', 'namespace MSP.Artifacts.SinkGatesData', '']
    for index in [*CONTROLS, *GADGETS]:
        sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
                 for side in artifact['constraints'][index]]
        lines += [f'def c{index} : Constraint :=', '  ⟨' + ', '.join(sides) + '⟩', '']
    for name, indices in [('controls', CONTROLS), ('gadgets', GADGETS)]:
        lines += [f'def {name} : List Constraint :=',
                  '  [' + ', '.join(f'c{i}' for i in indices) + ']', '']
    lines += ['end MSP.Artifacts.SinkGatesData', '']
    return '\n'.join(lines)


def check_symbols(sym, data):
    rows = symbol_rows(sym, parse_r1cs(data, pinned_compat=True))
    for k in range(2):
        expected = {
            f'main.out_inner[{k}]': 92 + k,
            f'main.out_value[{k}]': 94 + k,
            f'main.spend.outEqSink0[{k}].out': 13904 + 2*k,
            f'main.spend.outEqSink0[{k}].isz.inv': 13905 + 2*k,
            f'main.spend.outEqSink1[{k}].out': 13908 + 2*k,
            f'main.spend.outEqSink1[{k}].isz.inv': 13909 + 2*k,
            f'main.spend.outIsZero[{k}].out': 13912 + 2*k,
            f'main.spend.outIsZero[{k}].inv': 13913 + 2*k,
        }
        for name, wire in expected.items():
            require(rows[name]['wire'] == wire, f'wrong sink gadget wire for {name}')


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
        require(DESTINATION.read_bytes() == expected, 'SinkGatesData.lean differs from pinned constraints')
    print('SinkGatesData.lean matches exact pinned constraints 468..473 and 13856..13867.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
