#!/usr/bin/env python3
"""Audited extraction of the SPEC.md-pinned R1CS, not a proof of C1/C1c.

Binary layout: iden3/r1csfile doc/r1cs_bin_format.md. The default CLI accepts
only the full pinned digest. parse_r1cs() is strict unless explicitly allowed
to handle the exact pinned circom 2.0.8 section-count defect.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
PIN = 'e2f6fc89bc0e478231935d7dab10fb07316f2c6dab4303e95da1a390ce84f9bf'
SOURCE_PIN = '97c24b754549fd576c1e3d1e70345eba5570143895a0a9cceeb7e22176cdf8af'
LOCK_PIN = 'f64e99f822cfc5f09a047a79b7495432aef20a0f2b3d2f5b72d2d8f49b54b3db'
SYM_PIN = '10342e79bcec6e19ff64cb1ae34b433ab1780f926686e08828af1af78b1115f7'
ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / 'formal/Artifacts/spend.manifest.json'


class InvalidArtifact(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise InvalidArtifact(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


class Reader:
    def __init__(self, data, context):
        self.data, self.pos, self.context = data, 0, context

    def take(self, n):
        require(0 <= n <= len(self.data) - self.pos,
                f'{self.context}: truncated at byte {self.pos}, requested {n}')
        out = self.data[self.pos:self.pos + n]
        self.pos += n
        return out

    def integer(self, n):
        return int.from_bytes(self.take(n), 'little')

    def end(self):
        require(self.pos == len(self.data), f'{self.context}: trailing bytes')


def parse_r1cs(data, *, pinned_compat=False):
    r = Reader(data, 'file')
    require(r.take(4) == b'r1cs', 'bad magic')
    require(r.integer(4) == 1, 'unsupported R1CS version')
    declared = r.integer(4)
    require(declared in (3, 5), 'expected three sections (or pinned five-section defect)')
    sections, order = {}, []
    # Read complete section records to EOF, then check the declaration. Unknown
    # and custom-gate sections are intentionally outside this Groth16 profile.
    while r.pos < len(data):
        kind, size = r.integer(4), r.integer(8)
        require(kind in (1, 2, 3), f'unsupported section {kind}')
        require(kind not in sections, f'duplicate section {kind}')
        offset = r.pos
        sections[kind] = (r.take(size), offset)
        order.append(kind)
    require(set(sections) == {1, 2, 3}, 'missing required section')
    defect = declared != len(order)
    if defect:
        require(pinned_compat and sha(data) == PIN and declared == 5 and order == [2, 1, 3],
                'section count mismatch: declared five, actual three; only exact pinned artifact has compatibility allowance')
    h = Reader(sections[1][0], 'header')
    require(h.integer(4) == 32, 'field width must be 32 bytes')
    require(h.integer(32) == P, 'field order differs from Spec.Basic.p')
    names = ('wires', 'public_outputs', 'public_inputs', 'private_inputs', 'labels', 'constraints')
    header = dict(zip(names, (h.integer(4), h.integer(4), h.integer(4), h.integer(4), h.integer(8), h.integer(4))))
    h.end()
    n = header['wires']
    require(n > 0 and header['labels'] >= n, 'invalid wire/label counts')
    # Circom optimization can eliminate private inputs. nPrvIn describes source
    # inputs, not necessarily surviving wires, so do not require their sum <= n.
    require(1 + header['public_outputs'] + header['public_inputs'] <= n, 'public wire counts exceed wires')
    require(header['private_inputs'] < header['labels'], 'private input count exceeds labels')
    cr = Reader(sections[2][0], 'constraints')
    require(header['constraints'] <= len(cr.data) // 12, 'constraint count exceeds section capacity')
    constraints, term_count = [], 0
    for i in range(header['constraints']):
        constraint = []
        for side in 'ABC':
            count = cr.integer(4)
            require(count <= (len(cr.data) - cr.pos) // 36, f'constraint {i} {side}: term count exceeds remaining bytes')
            terms, seen = [], set()
            for _ in range(count):
                wire, coefficient = cr.integer(4), cr.integer(32)
                require(wire < n, f'constraint {i} {side}: wire out of range')
                require(wire not in seen, f'constraint {i} {side}: duplicate wire')
                require(coefficient < P, f'constraint {i} {side}: noncanonical coefficient')
                seen.add(wire)
                terms.append((wire, coefficient))
            term_count += count
            constraint.append(terms)
        constraints.append(constraint)
    cr.end()
    lr = Reader(sections[3][0], 'wire-to-label')
    require(len(lr.data) == 8 * n, 'wire-to-label section length mismatch')
    labels = [lr.integer(8) for _ in range(n)]
    require(labels[0] == 0, 'constant wire must map to label zero')
    require(len(set(labels)) == n and all(x < header['labels'] for x in labels), 'invalid or duplicate label')
    lr.end()
    return dict(header=header, constraints=constraints, labels=labels, terms=term_count,
                declared_sections=declared, section_count_defect=defect,
                sections=[dict(type=k, offset=sections[k][1], size=len(sections[k][0]), sha256=sha(sections[k][0])) for k in order])


def read_pinned(path):
    data = path.read_bytes()
    require(sha(data) == PIN, 'R1CS SHA-256 differs from canonical full pin')
    return data, parse_r1cs(data, pinned_compat=True)


def symbol_rows(data, artifact):
    require(sha(data) == SYM_PIN, 'symbol SHA-256 differs from reproduced pin')
    rows, labels, wires = {}, set(), set()
    for line in data.decode('utf-8').splitlines():
        parts = line.split(',')
        require(len(parts) == 4, 'malformed symbol row')
        label, wire, component = map(int, parts[:3])
        name = parts[3]
        require(name not in rows and label not in labels, 'duplicate symbol or label')
        require(0 < label < artifact['header']['labels'] and component >= 0, 'invalid symbol label/component')
        require(-1 <= wire < artifact['header']['wires'], 'symbol wire out of range')
        if wire >= 0:
            require(artifact['labels'][wire] == label, 'symbol contradicts R1CS wire-to-label section')
            require(wire not in wires, 'duplicate surviving symbol wire')
            wires.add(wire)
        labels.add(label)
        rows[name] = dict(label=label, wire=None if wire == -1 else wire, component=component)
    require(labels == set(range(1, artifact['header']['labels'])), 'incomplete symbol labels')
    require(wires == set(range(1, artifact['header']['wires'])), 'incomplete symbol wires')
    for wire, name in enumerate(('main.beta', 'main.gamma', 'main.alpha'), 1):
        require(rows[name]['wire'] == wire, 'public signal order mismatch')
    return rows


def selected_symbols(rows):
    names = ['main.beta', 'main.gamma', 'main.alpha']
    names += [f'main.stmt[{i}]' for i in range(10)]
    names += ['main.' + name for name in ('root', 'domain', 'public_amount', 'fee', 'recipient', 'authorizer')]
    for key in ('in_spend_key', 'in_rho', 'in_value', 'out_inner', 'out_value'):
        names += [f'main.{key}[{i}]' for i in range(2)]
    for key in ('in_siblings', 'in_bits'):
        names += [f'main.{key}[{i}][{j}]' for i in range(2) for j in range(20)]
    return {name: rows[name] for name in names}


def constraints_digest(constraints):
    """Cross-parser canonical form: decimal pairs sorted by wire, A;B;C per line."""
    digest = hashlib.sha256()
    for constraint in constraints:
        line = ';'.join(','.join(f'{w}:{c}' for w, c in sorted(side)) for side in constraint) + '\n'
        digest.update(line.encode('ascii'))
    return digest.hexdigest()


def summary(data, artifact):
    return dict(schema=1, artifact='build/spend.r1cs', sha256=sha(data), bytes=len(data),
                field_order=str(P), field_bytes=32, version=1,
                header=artifact['header'], terms=artifact['terms'],
                declared_sections=artifact['declared_sections'], sections=artifact['sections'],
                section_count_defect=artifact['section_count_defect'],
                circuit_sha256=SOURCE_PIN, toolchain_lock_sha256=LOCK_PIN,
                symbols_sha256=SYM_PIN, constraints_sha256=constraints_digest(artifact['constraints']))


def export_lean(data, destination):
    require(sha(data) == PIN, 'Lean export requires the exact pinned R1CS bytes')
    artifact = parse_r1cs(data, pinned_compat=True)
    # Numeric (wire, coefficient) pairs retain byte order, including any explicit
    # zero coefficient. Lean coerces coefficients to F only when evaluating.
    with destination.open('w', encoding='utf-8', newline='\n') as f:
        f.write('import Artifacts.R1CS\n\nnamespace MSP.Artifacts.Spend\n\n')
        f.write(f'-- Generated only from SHA-256 {PIN}.\n')
        f.write('-- This data file does not prove C1 or C1c.\n')
        f.write('set_option maxRecDepth 8192\n\n')
        chunks = []
        for start in range(0, len(artifact['constraints']), 8):
            name = f'chunk{start // 8}'
            chunks.append(name)
            f.write(f'def {name} : List Constraint := [\n')
            chunk = artifact['constraints'][start:start + 8]
            for index, constraint in enumerate(chunk):
                sides = ['[' + ', '.join(f'({w}, {c})' for w, c in terms) + ']' for terms in constraint]
                f.write('  ⟨' + ', '.join(sides) + '⟩' + (',' if index + 1 < len(chunk) else '') + '\n')
            f.write(']\n\n')
        groups = []
        for start in range(0, len(chunks), 32):
            name = f'group{start // 32}'
            groups.append(name)
            f.write(f'def {name} : List Constraint := List.flatten [' + ', '.join(chunks[start:start + 32]) + ']\n\n')
        f.write('def constraints : List Constraint := List.flatten [\n  ' + ', '.join(groups) + '\n]\n\n')
        f.write(f'def system : System := ⟨{artifact["header"]["wires"]}, constraints⟩\n')
        f.write('\nend MSP.Artifacts.Spend\n')


def check_lean(data, destination):
    """Require the checked-in Lean data to equal exact pinned-byte regeneration."""
    with tempfile.TemporaryDirectory(prefix='msp-lean-check-') as tmp:
        generated = Path(tmp) / 'Spend.lean'
        export_lean(data, generated)
        require(destination.read_bytes() == generated.read_bytes(),
                'Lean constraints differ from exact pinned-byte regeneration')


def reproduce(node_modules):
    node_modules = node_modules.resolve()
    for package, version in (('circom2', '0.2.8'), ('circomlib', '2.0.5')):
        require(json.loads((node_modules / package / 'package.json').read_text())['version'] == version,
                f'wrong {package} version')
    require(sha((ROOT / 'circuits/spend.circom').read_bytes()) == SOURCE_PIN, 'circuit source pin mismatch')
    require(sha((ROOT / 'tooling/package-lock.json').read_bytes()) == LOCK_PIN, 'toolchain lock pin mismatch')
    with tempfile.TemporaryDirectory(prefix='msp-r1cs-') as tmp:
        # circom2 0.2.8's WASI CLI resolves library directories correctly from the
        # package's parent, as in tooling/setup.sh. Never run setup's key ceremony.
        command = ['node', str(node_modules / 'circom2/cli.js'), str(ROOT / 'circuits/spend.circom'),
                   '--r1cs', '--sym', '-l', node_modules.name, '-o', tmp]
        subprocess.run(command, cwd=node_modules.parent, check=True, stdout=sys.stderr)
        data, artifact = read_pinned(Path(tmp) / 'spend.r1cs')
        sym = (Path(tmp) / 'spend.sym').read_bytes()
        rows = symbol_rows(sym, artifact)
        return data, artifact, rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--r1cs', type=Path, default=ROOT / 'build/spend.r1cs')
    ap.add_argument('--strict', action='store_true', help='reject even the pinned section-count defect')
    ap.add_argument('--reproduce', type=Path, metavar='NODE_MODULES', help='recompile pinned source, verify exact R1CS and symbols')
    ap.add_argument('--sym', type=Path, help='check a previously reproduced, pinned symbol file')
    lean_output = ap.add_mutually_exclusive_group()
    lean_output.add_argument('--export-lean', type=Path, help='write complete deterministic constraints, without semantic equivalence claims')
    lean_output.add_argument('--check-lean', type=Path, help='require exact byte-for-byte equality with regenerated Lean constraints')
    ap.add_argument('--write-manifest', action='store_true', help='explicitly regenerate manifest; requires --reproduce')
    args = ap.parse_args()
    data, artifact = read_pinned(args.r1cs)
    if args.strict:
        parse_r1cs(data)
    current = summary(data, artifact)
    require(sha((ROOT / 'circuits/spend.circom').read_bytes()) == SOURCE_PIN, 'circuit source pin mismatch')
    require(sha((ROOT / 'tooling/package-lock.json').read_bytes()) == LOCK_PIN, 'toolchain lock pin mismatch')
    rows = None
    if args.sym:
        rows = symbol_rows(args.sym.read_bytes(), artifact)
    if args.reproduce:
        reproduced_data, reproduced, rows = reproduce(args.reproduce)
        require(reproduced_data == data, 'recompiled R1CS bytes differ')
        require(reproduced == artifact, 'recompiled parsed constraints differ')
    if args.write_manifest:
        require(args.reproduce is not None, '--write-manifest requires reproduction')
        current['signals'] = selected_symbols(rows)
        MANIFEST.write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    else:
        saved = json.loads(MANIFEST.read_text())
        require({k: v for k, v in saved.items() if k != 'signals'} == current, 'manifest differs from exact parsed artifact')
        if rows is not None:
            require(saved['signals'] == selected_symbols(rows), 'manifest signal map differs from reproduced symbols')
    if args.export_lean:
        export_lean(data, args.export_lean)
    if args.check_lean:
        check_lean(data, args.check_lean)
    print(json.dumps(dict(sha256=PIN, wires=artifact['header']['wires'], constraints=artifact['header']['constraints'],
                         terms=artifact['terms'], symbols_checked=rows is not None, lean_checked=args.check_lean is not None,
                         pinned_section_count_exception=artifact['section_count_defect'],
                         result='artifact checked; C1/C1c and projections remain unproved'), sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
