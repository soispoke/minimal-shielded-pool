#!/usr/bin/env python3
"""Extract width-11 optimized Poseidon data and prepare checked algebra certificates."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
SOURCE_PIN = '94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee'
REFERENCE_PIN = 'aa4ff490f85bd66cdee8a926e24471d854f3e575d4fed354e0dbd550c77a59a2'
T = 11


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def matrix_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(T)) % P for j in range(T)]
            for i in range(T)]


def vector_mul(a, b):
    return [sum(a[k] * b[k][j] for k in range(T)) % P for j in range(T)]


def extract(source, name):
    body = source.split('function POSEIDON_' + name + '(', 1)[1]
    match = re.search(r'if\s*\(\s*t\s*==\s*11\s*\)\s*\{\s*return\s*', body)
    require(match is not None, f'missing width-11 {name}')
    start = body.index('[', match.end())
    depth = 0
    for end in range(start, len(body)):
        depth += (body[end] == '[') - (body[end] == ']')
        if depth == 0:
            return ast.literal_eval(body[start:end + 1])
    raise ValueError('unterminated constants')


def prepare(node_modules):
    raw = (node_modules / 'circomlib/circuits/poseidon_constants.circom').read_bytes()
    require(digest(raw) == SOURCE_PIN, 'optimized Circom constants changed')
    reference = (ROOT / 'reference/poseidon_bn254_constants.json').read_bytes()
    require(digest(reference) == REFERENCE_PIN, 'reference constants changed')
    C, M, pre, S = [extract(raw.decode(), n) for n in ('C', 'M', 'P', 'S')]
    ref = json.loads(reference)['t11']
    ref_c = list(map(int, ref['C']))
    ref_m = [list(map(int, row)) for row in ref['M']]
    require(len(C) == 154 and len(S) == 1386, 'wrong round data dimensions')
    require(M == list(map(list, zip(*ref_m))), 'matrix transpose mismatch')
    identity = [[int(i == j) for j in range(T)] for i in range(T)]
    sparse = []
    for r in range(66):
        s = S[r * 21:(r + 1) * 21]
        sparse.append([[int(i == j) if i and j else s[i] if j == 0 else s[10 + j]
                        for j in range(T)] for i in range(T)])
    prev, bases = identity, []
    for i in range(66):
        product = matrix_mul(M, prev)
        current = [[product[j][k] if j and k else int(j == k == 0)
                    for k in range(T)] for j in range(T)]
        require(matrix_mul(current, sparse[65 - i]) == product, f'sparse factor {i}')
        bases.append(current)
        prev = current
    require(matrix_mul(M, prev) == pre, 'prematrix factor')
    # Inversion only prepares witnesses. Lean checks multiplication identities.
    a = [row[:] + identity[i] for i, row in enumerate(M)]
    for j in range(T):
        pivot = next(k for k in range(j, T) if a[k][j])
        a[j], a[pivot] = a[pivot], a[j]
        inv = pow(a[j][j], -1, P)
        a[j] = [(x * inv) % P for x in a[j]]
        for i in range(T):
            if i != j:
                coefficient = a[i][j]
                a[i] = [(x - coefficient * y) % P for x, y in zip(a[i], a[j])]
    inverse = [row[T:] for row in a]
    require(matrix_mul(M, inverse) == identity, 'inverse witness')
    rounds = [ref_c[i:i + T] for i in range(0, len(ref_c), T)]
    accumulator, deltas = rounds[70], [[0] * T for _ in range(67)]
    for r in range(65, -1, -1):
        moved = vector_mul(accumulator, inverse)
        require(moved[0] == C[55 + r], f'partial constant {r}')
        deltas[r] = [0] + moved[1:]
        accumulator = [(x + y) % P for x, y in zip(rounds[r + 4], deltas[r])]
        require(vector_mul([C[55 + r]] + deltas[r][1:], M) ==
                [(x + y) % P for x, y in zip(rounds[r + 5], deltas[r + 1])],
                f'partial translation {r}')
    require(vector_mul(C[44:55], M) == accumulator, 'boundary translation')
    require(C[:11] == rounds[0], 'initial constants')
    for r in range(3):
        require(vector_mul(C[11 + 11*r:22 + 11*r], M) == rounds[r + 1], 'prefix constants')
        require(vector_mul(C[121 + 11*r:132 + 11*r], M) == rounds[71 + r], 'suffix constants')
    return C, M, pre, [S[i:i + 21] for i in range(0, len(S), 21)], sparse, list(reversed(bases)) + [identity], deltas


def lean(value):
    return '⟨#[' + ', '.join(map(lean, value)) + '], rfl⟩' if isinstance(value, list) else str(value)


def render(node_modules):
    C, M, pre, S, sparse, basis, delta = prepare(node_modules)
    lines = ['import Poseidon.Constants', 'import Mathlib.Data.Matrix.Mul',
             'import Mathlib.Data.Fin.VecNotation', '',
             '/-! Generated exact width-11 optimized constants and algebraic witnesses.',
             'The witnesses are checked by OptimizedCertificates; generation is not a proof. -/', '',
             'namespace MSP.Poseidon.Optimized', '',
             'abbrev State := Fin 11 → F',
             'abbrev Matrix11 := Matrix (Fin 11) (Fin 11) F', '',
             'set_option maxRecDepth 16384', '']
    for name, dims, typ, value in [('C', [154], 'Fin 154 → F', C),
             ('M', [11, 11], 'Matrix11', M), ('P', [11, 11], 'Matrix11', pre),
             ('S', [66, 21], 'Fin 66 → Fin 21 → F', S),
             ('sparseMatrix', [66, 11, 11], 'Fin 66 → Matrix11', sparse),
             ('basis', [67, 11, 11], 'Fin 67 → Matrix11', basis),
             ('translation', [67, 11], 'Fin 67 → State', delta)]:
        vector_type = 'F'
        for dim in reversed(dims):
            vector_type = f'Vector ({vector_type}) {dim}'
        args = ['r', 'i', 'j'][:len(dims)]
        access = name + 'Data'
        for arg in args:
            access = f'({access}.get {arg})'
        modifier = 'noncomputable ' if name == 'basis' else ''
        lines += [f'{modifier}def {name}Data : {vector_type} :=', '  ' + lean(value), '',
                  f'{modifier}def {name} : {typ} := fun {" ".join(args)} => {access}', '']
    lines += ['end MSP.Poseidon.Optimized', '']
    return '\n'.join(lines).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--node-modules', type=Path, default=ROOT / 'tooling/node_modules')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = render(args.node_modules)
    path = HERE / 'OptimizedData.lean'
    if args.check:
        require(path.read_bytes() == expected, 'OptimizedData differs from exact regeneration')
    else:
        path.write_bytes(expected)
    print('Width-11 optimized data and finite algebra certificates match pinned sources.')


if __name__ == '__main__':
    main()
