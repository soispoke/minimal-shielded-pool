#!/usr/bin/env python3
"""Generate checked width-3/4 specializations without modifying the width-11 proof."""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617
SOURCE_PIN = '94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee'
REFERENCE_PIN = 'aa4ff490f85bd66cdee8a926e24471d854f3e575d4fed354e0dbd550c77a59a2'
WIDTHS = {3: 57, 4: 56}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def matrix_mul(a, b):
    t = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(t)) % MODULUS
             for j in range(t)] for i in range(t)]


def vector_mul(a, b):
    return [sum(a[k] * b[k][j] for k in range(len(a))) % MODULUS
            for j in range(len(a))]


def extract(source, name, t):
    # Isolate this function, so a missing width cannot select a later function.
    body = source.split('function POSEIDON_' + name + '(', 1)[1].split('function ', 1)[0]
    match = re.search(r'if\s*\(\s*t\s*==\s*' + str(t) + r'\s*\)\s*\{\s*return\s*', body)
    require(match is not None, f'missing width-{t} {name}')
    start = body.index('[', match.end())
    depth = 0
    for end in range(start, len(body)):
        depth += (body[end] == '[') - (body[end] == ']')
        if depth == 0:
            return ast.literal_eval(body[start:end + 1])
    raise ValueError('unterminated constants')


def prepare(node_modules, t):
    require(t in WIDTHS, 'unsupported width')
    rp = WIDTHS[t]
    raw = (node_modules / 'circomlib/circuits/poseidon_constants.circom').read_bytes()
    require(digest(raw) == SOURCE_PIN, 'optimized Circom constants changed')
    reference = (ROOT / 'reference/poseidon_bn254_constants.json').read_bytes()
    require(digest(reference) == REFERENCE_PIN, 'reference constants changed')
    C, M, pre, S = [extract(raw.decode(), name, t) for name in ('C', 'M', 'P', 'S')]
    ref = json.loads(reference)[f't{t}']
    ref_c = list(map(int, ref['C']))
    ref_m = [list(map(int, row)) for row in ref['M']]
    require(len(ref_c) == t * (rp + 8), 'reference round count changed')
    require(len(C) == 8*t + rp and len(S) == rp * (2*t - 1), 'optimized round count changed')
    require(M == list(map(list, zip(*ref_m))), 'matrix transpose mismatch')
    identity = [[int(i == j) for j in range(t)] for i in range(t)]
    sparse = []
    for r in range(rp):
        s = S[r * (2*t - 1):(r + 1) * (2*t - 1)]
        sparse.append([[int(i == j) if i and j else s[i] if j == 0 else s[t - 1 + j]
                        for j in range(t)] for i in range(t)])
    prev, bases = identity, []
    for i in range(rp):
        product = matrix_mul(M, prev)
        current = [[product[j][k] if j and k else int(j == k == 0)
                    for k in range(t)] for j in range(t)]
        require(matrix_mul(current, sparse[rp - 1 - i]) == product, f'sparse factor {i}')
        bases.append(current)
        prev = current
    require(matrix_mul(M, prev) == pre, 'prematrix factor')
    # Inversion generates numeric witnesses; the Lean theorem needs only
    # multiplication identities, and does not trust this algorithm.
    a = [row[:] + identity[i] for i, row in enumerate(M)]
    for j in range(t):
        pivot = next(k for k in range(j, t) if a[k][j])
        a[j], a[pivot] = a[pivot], a[j]
        inv = pow(a[j][j], -1, MODULUS)
        a[j] = [(x * inv) % MODULUS for x in a[j]]
        for i in range(t):
            if i != j:
                coefficient = a[i][j]
                a[i] = [(x - coefficient * y) % MODULUS for x, y in zip(a[i], a[j])]
    inverse = [row[t:] for row in a]
    require(matrix_mul(M, inverse) == identity, 'inverse witness')
    rounds = [ref_c[i:i + t] for i in range(0, len(ref_c), t)]
    accumulator, deltas = rounds[rp + 4], [[0] * t for _ in range(rp + 1)]
    for r in range(rp - 1, -1, -1):
        moved = vector_mul(accumulator, inverse)
        require(moved[0] == C[5*t + r], f'partial constant {r}')
        deltas[r] = [0] + moved[1:]
        accumulator = [(x + y) % MODULUS for x, y in zip(rounds[r + 4], deltas[r])]
        require(vector_mul([C[5*t + r]] + deltas[r][1:], M) ==
                [(x + y) % MODULUS for x, y in zip(rounds[r + 5], deltas[r + 1])],
                f'partial translation {r}')
    require(vector_mul(C[4*t:5*t], M) == accumulator, 'boundary translation')
    require(C[:t] == rounds[0], 'initial constants')
    for r in range(3):
        require(vector_mul(C[t + t*r:2*t + t*r], M) == rounds[r + 1], 'prefix constants')
        lo = 5*t + rp + t*r
        require(vector_mul(C[lo:lo + t], M) == rounds[rp + 5 + r], 'suffix constants')
    return C, M, pre, [S[i:i + 2*t - 1] for i in range(0, len(S), 2*t - 1)], sparse, list(reversed(bases)) + [identity], deltas


def lean(value):
    return '⟨#[' + ', '.join(map(lean, value)) + '], rfl⟩' if isinstance(value, list) else str(value)


def data_file(node_modules, t):
    rp = WIDTHS[t]
    C, M, pre, S, sparse, basis, delta = prepare(node_modules, t)
    lines = ['import Poseidon.Constants', 'import Mathlib.Data.Matrix.Mul', '',
             f'/-! Generated width-{t} optimized data and algebraic witnesses.',
             f'Circom constants SHA-256: {SOURCE_PIN}.',
             f'Reference constants SHA-256: {REFERENCE_PIN}.',
             'The witnesses are checked in Lean; generation is not a proof. -/', '',
             f'namespace MSP.Poseidon.Optimized{t}', '',
             f'abbrev State := Fin {t} → F',
             f'abbrev Matrix{t} := Matrix (Fin {t}) (Fin {t}) F', '',
             'set_option maxRecDepth 16384', '']
    for name, dims, typ, value in [
            ('C', [8*t + rp], f'Fin {8*t + rp} → F', C),
            ('M', [t, t], f'Matrix{t}', M), ('P', [t, t], f'Matrix{t}', pre),
            ('S', [rp, 2*t - 1], f'Fin {rp} → Fin {2*t - 1} → F', S),
            ('sparseMatrix', [rp, t, t], f'Fin {rp} → Matrix{t}', sparse),
            ('basis', [rp + 1, t, t], f'Fin {rp + 1} → Matrix{t}', basis),
            ('translation', [rp + 1, t], f'Fin {rp + 1} → State', delta)]:
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
    lines += [f'end MSP.Poseidon.Optimized{t}', '']
    return '\n'.join(lines).encode()


def specialize(source, t):
    rp = WIDTHS[t]
    # Token replacements specialize only the width-11 schedule parameters.
    values = {154: 8*t + rp, 121: 5*t + rp, 74: rp + 8, 73: rp + 7,
              71: rp + 5, 70: rp + 4, 67: rp + 1, 66: rp, 55: 5*t, 11: t, 10: t - 1}
    source = re.sub(r'\b(?:' + '|'.join(map(str, values)) + r')\b',
                    lambda match: str(values[int(match[0])]), source)
    source = source.replace('Poseidon.Optimized', f'Poseidon.Optimized{t}')
    source = source.replace('Matrix11', f'Matrix{t}').replace('params11', f'params{t}')
    source = source.replace('hash10', f'hash{t - 1}')
    ordinary = f'MSP.Poseidon.hash{t - 1}'
    applied = ordinary + ' ' + ' '.join(f'(inputs {i})' for i in range(t - 1))
    source = source.replace(ordinary + ' inputs', applied)
    return source


def outputs(node_modules):
    result = {}
    for t, rp in WIDTHS.items():
        result[f'Optimized{t}Data.lean'] = data_file(node_modules, t)
        for suffix in ('', 'Certificates', 'Reference', 'Equivalence'):
            source = specialize((HERE / f'Optimized{suffix}.lean').read_text(), t)
            if suffix == 'Reference':
                old = f'    unfold MSP.Poseidon.hash{t - 1} hash referenceState\n'
                new = (f'    have hi : (Vector.ofFn inputs : Vector F {t - 1}) =\n'
                       '        ⟨#[' + ', '.join(f'inputs {i}' for i in range(t - 1)) + '], rfl⟩ := by\n'
                       '      apply Vector.ext\n'
                       '      intro i hi\n'
                       '      interval_cases i <;> rfl\n'
                       f'    unfold MSP.Poseidon.hash{t - 1}\n'
                       '    rw [← hi]\n'
                       '    unfold hash referenceState\n')
                require(old in source, 'reference template changed')
                source = source.replace(old, new)
            source = '/- Generated by small_optimized_generate.py from the checked width-11 proof. -/\n' + source
            result[f'Optimized{t}{suffix}.lean'] = source.encode()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--node-modules', type=Path, default=ROOT / 'tooling/node_modules')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, expected in outputs(args.node_modules).items():
        path = HERE / name
        if args.check:
            require(path.read_bytes() == expected, f'{name} differs from exact regeneration')
        else:
            path.write_bytes(expected)
    print('Width-3/4 optimized data, certificates and proof specializations match pinned sources.')


if __name__ == '__main__':
    main()
