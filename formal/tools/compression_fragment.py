#!/usr/bin/env python3
"""Generate/check the exact first nine pinned R1CS constraints as Lean data."""
import argparse
import sys
from r1cs_artifact import InvalidArtifact, PIN, ROOT, parse_r1cs, require, sha

DESTINATION = ROOT / 'formal/Artifacts/CompressionData.lean'


def render(data):
    require(sha(data) == PIN, 'fragment requires exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    lines = ['import Artifacts.R1CS', '', '/-!', '# Exact pinned compression constraints', '',
             f'Generated from SHA-256 `{PIN}`, constraint indices 0 through 8.',
             'Regenerate with `python3 formal/tools/compression_fragment.py --write`.',
             'The entire R1CS remains the source artifact; this is only its prefix.',
             '-/', '', 'namespace MSP.Artifacts.CompressionData', '']
    for index, constraint in enumerate(artifact['constraints'][:9]):
        sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
                 for side in constraint]
        lines.extend([f'def c{index} : Constraint :=', '  ⟨' + ', '.join(sides) + '⟩', ''])
    lines.extend(['def constraints : List Constraint :=',
                  '  [' + ', '.join(f'c{i}' for i in range(9)) + ']', '',
                  'end MSP.Artifacts.CompressionData', ''])
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='explicitly regenerate the checked-in Lean data')
    args = parser.parse_args()
    expected = render((ROOT / 'build/spend.r1cs').read_bytes()).encode('utf-8')
    if args.write:
        DESTINATION.write_bytes(expected)
    else:
        require(DESTINATION.read_bytes() == expected, 'CompressionData.lean differs from exact constraints 0..8')
    print('CompressionData.lean matches exact pinned constraints 0..8.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
