#!/usr/bin/env python3
"""Extract exact beta S-box triples and affine stage certificates from the pinned R1CS."""
import argparse
from pathlib import Path
import sys
from r1cs_artifact import P, PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha, symbol_rows

sys.path.insert(0, str(ROOT / 'formal/Poseidon'))
import optimized_generate as optimized

DESTINATION = ROOT / 'formal/Artifacts/BetaGatesData.lean'


def add(*forms):
    result = {}
    for form in forms:
        for wire, coefficient in form:
            result[wire] = (result.get(wire, 0) + coefficient) % P
    return sorted((wire, coefficient) for wire, coefficient in result.items() if coefficient)


def scale(c, form):
    return add([(wire, c * coefficient) for wire, coefficient in form])


def mix(matrix, state):
    return [add(*(scale(matrix[j][i], state[j]) for j in range(11))) for i in range(11)]


def prepare(data, node_modules):
    require(sha(data) == PIN, 'beta gates require exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    C, M, pre, _, sparse, _, _ = optimized.prepare(node_modules)
    constraints = artifact['constraints'][9:468]
    triples = [constraints[3*i:3*i+3] for i in range(153)]
    for i, (c0, c1, c2) in enumerate(triples):
        require(add(c0[0]) == scale(-1, c0[1]), f'triple {i}: square input sign')
        require(add(c0[2]) == scale(-1, c1[1]), f'triple {i}: square output sign')
        require(add(c1[0]) == scale(-1, c1[1]), f'triple {i}: fourth input sign')
        require(add(c2[0]) == add(c1[2]), f'triple {i}: fourth output sign')
        require(add(c2[1]) == add(c0[1]), f'triple {i}: fifth input')
    full_in, full_out = [], []
    for r in range(8):
        ins, outs = [], []
        for j in range(11):
            if r == j == 0:
                ins.append([(0, C[0])])
                outs.append([(0, pow(C[0], 5, P))])
            else:
                t = j - 1 if r == 0 else 10 + 11*(r-1) + j
                ins.append(add(triples[t][0][1]))
                outs.append(scale(-1, triples[t][2][2]))
        full_in.append(ins)
        full_out.append(outs)
    inputs = [[(w, 1)] for w in [99, 100, 101, 102, 4, 5, 96]]
    inputs += [[(10, 1), (11, 1), (94, P-1), (95, P-1), (96, P-1)]]
    inputs += [[(w, 1)] for w in [97, 98]]
    require(full_in[0] == [[(0, C[0])]] + [add(f, [(0, C[j+1])]) for j, f in enumerate(inputs)],
            'initial state mismatch')
    for r in range(3):
        expected = mix(M, [add(f, [(0, C[11+11*r+j])]) for j, f in enumerate(full_out[r])])
        require(full_in[r+1] == expected, f'prefix {r}')
    state = mix(pre, [add(f, [(0, C[44+j])]) for j, f in enumerate(full_out[3])])
    partials = [state]
    for r in range(66):
        require(state[0] == add(triples[87+r][0][1]), f'partial input {r}')
        out = scale(-1, triples[87+r][2][2])
        state = mix(sparse[r], [add(out, [(0, C[55+r])])] + state[1:])
        partials.append(state)
    require(state == full_in[4], 'partial/suffix boundary')
    for r in range(3):
        expected = mix(M, [add(f, [(0, C[121+11*r+j])]) for j, f in enumerate(full_out[4+r])])
        require(full_in[5+r] == expected, f'suffix {r}')
    require(mix(M, full_out[7])[0] == [(1, 1)], 'final beta wire')
    return constraints, full_in, full_out, partials


def lean_form(form):
    return '[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in form) + ']'


def render(data, node_modules):
    constraints, full_in, full_out, partials = prepare(data, node_modules)
    lines = ['import Artifacts.BetaGatesLemmas', '', '/-!', '# Exact beta constraint data', '',
             f'Pinned R1CS SHA-256 `{PIN}`, constraints 9 through 467.',
             'Affine witnesses are checked by BetaGatesCertificates, not trusted as generated facts.',
             'Regenerate with `python3 formal/tools/beta_gates.py --write --node-modules PATH`.',
             '-/', '', 'namespace MSP.Artifacts.BetaGatesData', '',
             'open MSP.Artifacts.BetaGates', 'set_option maxRecDepth 16384', '']
    for start in range(0, len(constraints), 8):
        block = constraints[start:start+8]
        lines += [f'def block{start//8} : List Constraint := [']
        for i, constraint in enumerate(block):
            lines += ['  ⟨' + ', '.join(lean_form(side) for side in constraint) + '⟩' +
                      (',' if i < len(block)-1 else '')]
        lines += [']', '']
    lines += ['def constraints : List Constraint :=',
              '  [' + ', '.join(f'block{i}' for i in range((len(constraints)+7)//8)) + '].flatten', '',
              'theorem constraints_length : constraints.length = 459 := rfl', '',
              'def triple (t : Fin 153) (j : Fin 3) : Constraint :=',
              "  constraints[3 * t.val + j.val]'(by rw [constraints_length]; omega)", '',
              'def input (t : Fin 153) : Form := ofLC (triple t 0).b',
              'def output (t : Fin 153) : Form := scale (-1) (ofLC (triple t 2).c)', '']
    for name, states in [('fullInput', full_in), ('fullOutput', full_out), ('partialInput', partials)]:
        for r, state in enumerate(states):
            lines += [f'def {name}{r} : Fin 11 → Form :=',
                      '  ![' + ',\n    '.join(lean_form(f) for f in state) + ']', '']
        # An array avoids deeply nested function/vector notation for 67 states.
        lines += [f'def {name}Data : Vector (Fin 11 → Form) {len(states)} :=',
                  '  ⟨#[' + ', '.join(f'{name}{r}' for r in range(len(states))) + '], rfl⟩',
                  f'def {name} (r : Fin {len(states)}) : Fin 11 → Form := {name}Data.get r', '']
    lines += ['end MSP.Artifacts.BetaGatesData', '']
    return '\n'.join(lines)


def check_symbols(sym, data):
    rows = symbol_rows(sym, parse_r1cs(data, pinned_compat=True))
    require(rows['main.beta']['wire'] == 1, 'beta output wire mismatch')
    expected = {f'main.stmt[{i}]': 99+i for i in range(4)}
    expected.update({'main.root': 4, 'main.domain': 5, 'main.public_amount': 96,
                     'main.fee': None, 'main.recipient': 97, 'main.authorizer': 98,
                     'main.in_value[0]': 10, 'main.in_value[1]': 11,
                     'main.out_value[0]': 94, 'main.out_value[1]': 95})
    for name, wire in expected.items():
        require(rows[name]['wire'] == wire, f'wrong statement field wire for {name}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--node-modules', type=Path, default=ROOT / 'tooling/node_modules')
    parser.add_argument('--sym', type=Path)
    args = parser.parse_args()
    data = (ROOT / 'build/spend.r1cs').read_bytes()
    expected = render(data, args.node_modules).encode()
    if args.sym:
        check_symbols(args.sym.read_bytes(), data)
    if args.write:
        DESTINATION.write_bytes(expected)
    else:
        require(DESTINATION.read_bytes() == expected, 'BetaGatesData.lean differs from exact regeneration')
    print('Beta data matches 153 exact S-box triples and all optimized affine stages.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
