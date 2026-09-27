#!/usr/bin/env python3
"""Executable counterexamples for the four SPEC C1 circuit mutations.

Build only temporary source copies. Never regenerate keys or change the pinned
R1CS parser. Mutants are decoded by pinned r1csfile; Python independently reads
WTNS and evaluates every decoded modular equation. This is finite executable
evidence, not a Lean theorem about a mutated circuit.
"""
from __future__ import annotations
import argparse
import copy
import difflib
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tarfile
import tempfile

import r1cs_artifact as pinned

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'reference'))
from poseidon_bn254 import P, p2, p3, poseidon

MODULES = Path('/Volumes/PrivateAI/WorkRepos/minimal-shielded-pool/tooling/node_modules')
DEFAULT_EVIDENCE = ROOT / 'formal/evidence/2026-09-27-0350/circuit-mutations'
PACKAGES = {'circom2': '0.2.8', 'circomlib': '2.0.5', 'circomlibjs': '0.1.7',
            'snarkjs': '0.7.5', 'r1csfile': '0.0.48', 'ffjavascript': '0.2.63'}
EXPECTED_FAILURE = {'baseline': [], 'membership': ['R3'], 'range': ['R5'],
                    'duplicate': ['R8'], 'sink': ['R7']}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def decimals(value):
    if isinstance(value, int):
        return str(value)
    if isinstance(value, list):
        return [decimals(v) for v in value]
    if isinstance(value, dict):
        return {k: decimals(v) for k, v in value.items()}
    return value


def replace_once(source, old, new):
    require(source.count(old) == 1, f'expected exactly one mutation site: {old!r}')
    return source.replace(old, new, 1)


def mutate(source, name):
    if name == 'baseline':
        return source
    if name == 'membership':
        return replace_once(source, '    (cur[DEPTH] - root) * value === 0;\n', '')
    if name == 'range':
        return replace_once(source, '    for (var k = 0; k < 6; k++) {',
                            '    for (var k = 1; k < 6; k++) {')
    if name == 'duplicate':
        return replace_once(source, '    sameNullifier.out === 0;\n', '')
    if name == 'sink':
        source = replace_once(source, '''        if (k == 0) {
            (out_inner[k] - SINK_INNER_0) * outIsZero[k].out === 0;
        } else {
            (out_inner[k] - SINK_INNER_1) * outIsZero[k].out === 0;
        }
''', '')
        for sink in (0, 1):
            source = replace_once(source,
                f'        outEqSink{sink}[k].out * (1 - outIsZero[k].out) === 0;\n', '')
        return source
    raise ValueError(name)


def merkle(leaf, bits, siblings):
    for bit, sibling in zip(bits, siblings, strict=True):
        require(bit in (0, 1), 'non-Boolean path input')
        leaf = p2(sibling, leaf) if bit else p2(leaf, sibling)
    return leaf


def input_cases():
    zeros = [0]
    for _ in range(20):
        zeros.append(p2(zeros[-1], zeros[-1]))
    base = dict(alpha=0, domain=1, in_spend_key=[1, 2], in_rho=[1, 2],
                in_value=[2, 0], in_siblings=[zeros[:20], [0] * 20],
                in_bits=[[0] * 20, [0] * 20], out_inner=[1, 2], out_value=[0, 0],
                public_amount=1, fee=1, recipient=1, authorizer=1)
    base['root'] = merkle(p3(2, p2(p3(1, 1, 0), 1), 2), base['in_bits'][0], zeros[:20])
    result = {name: copy.deepcopy(base) for name in EXPECTED_FAILURE}
    result['membership']['root'] = 0
    result['range'].update(in_value=[2**128, 0], out_inner=[3, 2],
                           out_value=[2**128 - 1, 0], public_amount=0, recipient=0)
    result['range']['root'] = merkle(p3(2, p2(p3(1, 1, 0), 1), 2**128), [0] * 20, zeros[:20])
    result['duplicate'].update(in_spend_key=[1, 1], in_rho=[1, 1], in_value=[1, 1],
                               in_siblings=[zeros[:20], zeros[:20]])
    result['duplicate']['root'] = merkle(p3(2, p2(p3(1, 1, 0), 1), 1), [0] * 20, zeros[:20])
    result['sink']['out_inner'] = [3, 2]
    return result


def semantics(inp, actual_statement=None):
    """R1--R9 on canonical integer representatives; outputs come from WTNS."""
    indices = [sum(bit * 2**i for i, bit in enumerate(bits)) for bits in inp['in_bits']]
    leaves = [p3(2, p2(p3(1, sk, 0), rho), value)
              for sk, rho, value in zip(inp['in_spend_key'], inp['in_rho'], inp['in_value'], strict=True)]
    nullifiers = [p3(4, p2(inp['domain'], sk), p2(leaf, index))
                  for sk, leaf, index in zip(inp['in_spend_key'], leaves, indices, strict=True)]
    outputs = [p3(2, inner, value) for inner, value in zip(inp['out_inner'], inp['out_value'], strict=True)]
    expected = nullifiers + outputs + [inp[k] for k in ('root', 'domain', 'public_amount', 'fee', 'recipient', 'authorizer')]
    statement = expected if actual_statement is None else actual_statement
    require(statement == expected, 'actual statement disagrees with independent Poseidon/source projection')
    roots = [merkle(leaf, bits, siblings) for leaf, bits, siblings in
             zip(leaves, inp['in_bits'], inp['in_siblings'], strict=True)]
    amounts = inp['in_value'] + inp['out_value'] + statement[6:8]
    ranges = [0 <= v < 2**128 for v in amounts]
    conservation = sum(inp['in_value']) == sum(inp['out_value']) + statement[6] + statement[7]
    clauses = {
        'R1': all(0 <= i < 2**20 for i in indices),
        'R2': statement[:2] == nullifiers,
        'R3': all(v == 0 or root == statement[4] for v, root in zip(inp['in_value'], roots, strict=True)),
        'R4': statement[2:4] == outputs,
        'R5': all(ranges) and conservation,
        'R6': sum(inp['in_value']) > 0,
        'R7': all(inner == k + 1 if value == 0 else inner not in (1, 2)
                  for k, (inner, value) in enumerate(zip(inp['out_inner'], inp['out_value'], strict=True))),
        'R8': statement[0] != statement[1] and statement[2] != statement[3],
        'R9': 0 <= statement[8] < 2**160 and 0 < statement[9] < 2**160 and
              ((statement[6] == 0) == (statement[8] == 0)),
    }
    beta = poseidon(statement)
    sigma = (inp['alpha'] + beta) % P
    gamma = sum(value * pow(sigma, i, P) for i, value in enumerate(statement)) % P
    return dict(clauses=clauses, failed_clauses=[k for k, v in clauses.items() if not v],
                amount_ranges=ranges, integer_conservation=conservation,
                indices=indices, leaves=decimals(leaves), computed_roots=decimals(roots),
                statement=decimals(statement), public_signals=decimals([beta, gamma, inp['alpha']]))


def read_wtns(path):
    """Independent strict WTNS v2 decoder, including length and canonicality."""
    r = pinned.Reader(path.read_bytes(), 'WTNS file')
    require(r.take(4) == b'wtns' and r.integer(4) == 2, 'expected WTNS v2')
    require(r.integer(4) == 2, 'expected exactly two WTNS sections')
    sections = {}
    for _ in range(2):
        kind, size = r.integer(4), r.integer(8)
        require(kind in (1, 2) and kind not in sections, 'bad WTNS section')
        sections[kind] = r.take(size)
    r.end()
    h = pinned.Reader(sections[1], 'WTNS header')
    require(h.integer(4) == 32 and h.integer(32) == P, 'WTNS field mismatch')
    count = h.integer(4)
    h.end()
    require(len(sections[2]) == 32 * count, 'WTNS payload length mismatch')
    values = [int.from_bytes(sections[2][32*i:32*(i+1)], 'little') for i in range(count)]
    require(all(v < P for v in values) and values[0] == 1, 'noncanonical WTNS or bad constant wire')
    return values


def check_constraints(decoded, values):
    require(int(decoded['prime']) == P and decoded['wires'] == len(values), 'R1CS/WTNS field or wire mismatch')
    require(decoded['constraint_count'] == len(decoded['constraints']), 'constraint count mismatch')
    require([int(v) for v in decoded['witness']] == values, 'independent WTNS decoder disagrees with snarkjs')
    failures, terms = [], 0
    for index, constraint in enumerate(decoded['constraints']):
        require(len(constraint) == 3, 'bad equation shape')
        evaluated = []
        for side in constraint:
            seen = set()
            acc = 0
            for wire, coefficient in side:
                coefficient = int(coefficient)
                require(0 <= wire < len(values) and wire not in seen and 0 <= coefficient < P,
                        'invalid decoded coefficient')
                seen.add(wire)
                acc += coefficient * values[wire]
                terms += 1
            evaluated.append(acc % P)
        if (evaluated[0] * evaluated[1] - evaluated[2]) % P:
            failures.append(index)
    require(not failures, f'independent Python constraint failures: {failures}')
    return dict(constraints_checked=len(decoded['constraints']), coefficients_checked=terms,
                failed_constraints=failures, wire_zero_is_one=values[0] == 1,
                independently_decoded_witness_matches=True)


def project(inp, sym, values):
    rows = {}
    for line in sym.read_text().splitlines():
        label, wire, component, name = line.split(',')
        rows[name] = int(wire)
    def get(name):
        require(rows.get(name, -1) >= 0, f'expected surviving symbol {name}')
        return values[rows[name]]
    # Read each surviving source signal, including all private path values.
    for key, value in inp.items():
        def walk(v, name):
            if isinstance(v, list):
                for i, child in enumerate(v):
                    walk(child, f'{name}[{i}]')
            elif rows.get(name, -1) >= 0:
                require(get(name) == v, f'actual input differs at {name}')
            else:
                require(name == 'main.fee', f'unexpected eliminated source input {name}')
        walk(value, 'main.' + key)
    # Fee is the actual concrete projection used in Artifacts.Witness: it was
    # eliminated by conservation. Read it from the surviving amount wires.
    fee = (get('main.in_value[0]') + get('main.in_value[1]') - get('main.out_value[0]') -
           get('main.out_value[1]') - get('main.public_amount')) % P
    require(fee == inp['fee'], 'eliminated fee projection mismatch')
    statement = [get(f'main.stmt[{i}]') for i in range(4)] + [get('main.root'), get('main.domain'),
                 get('main.public_amount'), fee, get('main.recipient'), get('main.authorizer')]
    return statement, [get('main.beta'), get('main.gamma'), get('main.alpha')]


def run(command, cwd, log, *, succeeds=True):
    completed = subprocess.run([str(c) for c in command], cwd=cwd, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
    log.write_text(completed.stdout)
    record = dict(command=[str(c) for c in command], cwd=str(cwd), exit_code=completed.returncode,
                  output_sha256=sha(log), log=log.name)
    if succeeds:
        require(completed.returncode == 0, f'command failed; see {log}')
    else:
        require(completed.returncode != 0 and 'Assert Failed' in completed.stdout,
                f'expected original circuit assertion failure; see {log}')
    return record


def archive_files(destination, files):
    # Preserve the actual raw source/R1CS/WTNS/symbol bytes, deterministic gzip.
    with destination.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0, filename='') as gz:
        with tarfile.open(fileobj=gz, mode='w') as archive:
            for name, path in files:
                data = path.read_bytes()
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--node-modules', type=Path, default=MODULES)
    parser.add_argument('--evidence', type=Path, default=DEFAULT_EVIDENCE)
    args = parser.parse_args()
    modules, evidence = args.node_modules.resolve(), args.evidence.resolve()
    require(not (evidence / 'results.json').exists(), 'refuse to overwrite completed evidence; choose a new --evidence directory')
    evidence.mkdir(parents=True, exist_ok=True)
    require(sha(ROOT / 'circuits/spend.circom') == pinned.SOURCE_PIN, 'source pin mismatch')
    require(sha(ROOT / 'tooling/package-lock.json') == pinned.LOCK_PIN, 'lockfile pin mismatch')
    for pkg, version in PACKAGES.items():
        require(json.loads((modules / pkg / 'package.json').read_text())['version'] == version, f'{pkg} version mismatch')
    provenance = dict(source_sha256=pinned.SOURCE_PIN, lock_sha256=pinned.LOCK_PIN,
                      baseline_r1cs_sha256=pinned.PIN, baseline_symbols_sha256=pinned.SYM_PIN,
                      packages=PACKAGES, node_modules=str(modules),
                      git_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                      node_version=subprocess.check_output(['node', '--version'], text=True).strip(),
                      python_version=sys.version, file_hashes={})
    for path in [Path(__file__), Path(__file__).with_suffix('.cjs'),
                 ROOT / 'formal/tools/r1cs_artifact.py', ROOT / 'reference/poseidon_bn254.py',
                 ROOT / 'reference/poseidon_bn254_constants.json', ROOT / 'formal/Spec/Relation.lean',
                 modules / 'circom2/cli.js', modules / 'circom2/circom.wasm',
                 modules / 'r1csfile/build/main.cjs', modules / 'snarkjs/build/main.cjs'] + sorted((modules / 'circomlib/circuits').rglob('*.circom')):
        provenance['file_hashes'][str(path)] = sha(path)
    temporary = Path(tempfile.mkdtemp(prefix='msp-circuit-mutations-', dir='/private/tmp'))
    provenance['temporary_directory'] = str(temporary)
    write_json(evidence / 'provenance.json', provenance)
    original = (ROOT / 'circuits/spend.circom').read_text()
    cases, results = input_cases(), {}
    for name, inp in cases.items():
        print(f'{name}: compiling and checking', flush=True)
        build, saved = temporary / name, evidence / name
        build.mkdir(); saved.mkdir(exist_ok=True)
        source = build / 'spend.circom'
        source.write_text(mutate(original, name))
        (saved / 'source.patch').write_text(''.join(difflib.unified_diff(original.splitlines(True),
            source.read_text().splitlines(True), fromfile='pinned/spend.circom', tofile=f'{name}/spend.circom')))
        input_path = saved / 'input.json'
        write_json(input_path, decimals(inp))
        result = dict(source_sha256=sha(source), input_sha256=sha(input_path), commands=[])
        result['commands'].append(run(['node', modules / 'circom2/cli.js', source, '--r1cs', '--sym', '--wasm',
            '-l', modules.name, '-o', build], modules.parent, saved / 'compile.log'))
        r1cs, symbols, witness = build / 'spend.r1cs', build / 'spend.sym', build / 'witness.wtns'
        if name == 'baseline':
            require(sha(r1cs) == pinned.PIN and sha(symbols) == pinned.SYM_PIN, 'baseline artifact reproduction mismatch')
            pinned.read_pinned(r1cs)
        result['commands'].append(run(['node', build / 'spend_js/generate_witness.js', build / 'spend_js/spend.wasm',
            input_path, witness], build, saved / 'witness.log'))
        decoded_path = build / 'decoded.json'
        result['commands'].append(run(['node', Path(__file__).with_suffix('.cjs'), modules, r1cs, witness, decoded_path],
                                     build, saved / 'snarkjs-check.log'))
        decoded = json.loads(decoded_path.read_text())
        values = read_wtns(witness)
        result['python_check'] = check_constraints(decoded, values)
        statement, public = project(inp, symbols, values)
        result['semantics'] = semantics(inp, statement)
        require([str(v) for v in public] == result['semantics']['public_signals'], 'compression witness mismatch')
        require(result['semantics']['failed_clauses'] == EXPECTED_FAILURE[name], 'unexpected semantic failures')
        result['snarkjs_check'] = decoded['snarkjs_check']
        result['artifact'] = {p.name: dict(sha256=sha(p), bytes=p.stat().st_size)
                              for p in (r1cs, witness, symbols, build / 'spend_js/spend.wasm')}
        result['decoded_constraints_sha256'] = pinned.constraints_digest(decoded['constraints'])
        if name != 'baseline':
            baseline = temporary / 'baseline'
            result['original_rejection'] = run(['node', baseline / 'spend_js/generate_witness.js',
                baseline / 'spend_js/spend.wasm', input_path, build / 'original-rejected.wtns'],
                baseline, saved / 'original-rejection.log', succeeds=False)
        archive = saved / 'artifacts.tar.gz'
        archive_files(archive, [(p.name, p) for p in (source, r1cs, symbols, witness)] +
                      [('spend.wasm', build / 'spend_js/spend.wasm')])
        result['archive_sha256'] = sha(archive)
        write_json(saved / 'result.json', result)
        results[name] = result
        print(f'{name}: {decoded["constraint_count"]} constraints PASS; failing relation clauses: {EXPECTED_FAILURE[name]}', flush=True)
    write_json(evidence / 'results.json', results)
    print(f'All five cases passed. Evidence: {evidence}', flush=True)


if __name__ == '__main__':
    main()
