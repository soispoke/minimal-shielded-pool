#!/usr/bin/env python3
"""Export full, kernel-checkable assignments for the four archived mutants.

The exact raw artifacts remain unchanged. These Circom files share the known
five-versus-three section-count defect. Only for the four full hashes below,
normalize that one header word in memory and apply the existing strict parser.
Every constraint is also compared with the archived independent JS decoding.
This exporter is an external artifact binding, not a verified binary parser.
"""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile
import tempfile

import circuit_mutations as m
import r1cs_artifact as r

ROOT = Path(__file__).resolve().parents[2]
EVIDENCE = ROOT / 'formal/evidence/2026-09-27-0350/circuit-mutations'
PINS = {
    'membership': '0e9f060320e989a7bbc4dc34ea92f58a4b48c24cabf79a64caca9b928f2c9184',
    'range': 'd1156919fe5237c7f28d54d538750fce0913dc386b48fcea94581917deef56a3',
    'duplicate': 'ee86ff80bb161e71894de9fe3d576469bab5ad56aded622804dffbddf26318df',
    'sink': '1051e2912a70a5063df35b98069c3caee2877164aafab05c838ab22b8662147a',
}
# Hashes of each archived run, pinned here rather than read from the unowned
# evidence directory: the archive, the symbol file that names the projection
# wires, the witness, and the independent JS decoding digest.
RECORD_PINS = {
    'membership': {'archive': 'fb5a38bf2800a55c0396363e717b8733a5b44af19d7e0a3ead52400b3fdf2333',
                  'spend.sym': '10342e79bcec6e19ff64cb1ae34b433ab1780f926686e08828af1af78b1115f7',
                  'witness.wtns': 'e26e3ddfba36774f5b9c19d080cc8b5a31580972da1045b7774392d6ed5d844b',
                  'decoded': '91ce72fa3fbc89d321338d6c7ffcc015a5483c62226bfd4d086bd4fbc8b413b9'},
    'range': {'archive': '5bb68f8fea2b816c0606202c5d06a4c737c107c85e9a294b78a93bdd54e7c7c1',
             'spend.sym': 'b17c0904207dea20d994486f99d20f676164fd3627f9ac572c434ca484983c55',
             'witness.wtns': 'bb77cffbdda58e311171f957809556a78614e1fe79e3347c00622ff282984cce',
             'decoded': '19410bf2b20ef4f4fc0ae1ceb5206a7eac48dd38a3ddbcba344a6a08f9665ecc'},
    'duplicate': {'archive': '63a61b2705faea1468979cbfbbf857e1d572ef7b16c83987b2826ea7848db23c',
                 'spend.sym': 'a636690db77104d2dc6dd16bda7591742eff7faa87dc258a44fe5f673bbe99e9',
                 'witness.wtns': '456dce5c0d5c1be1ac943fd8bb291bc281f12fb1e050bea4144305da527db035',
                 'decoded': '15eae9b64ed0d396a7540e377da7361082f38a7d1b5f392d5fdc7802f164e868'},
    'sink': {'archive': '84da0a06a924c7a1ce8dcd1c51c0d553e362402f6848eddfaeb4224ded2cf1f8',
            'spend.sym': '10342e79bcec6e19ff64cb1ae34b433ab1780f926686e08828af1af78b1115f7',
            'witness.wtns': 'd870b1c73770add827567429099cf1c8a41e3808f5d6e03ee18f348d4650f596',
            'decoded': 'e1cef9d22a21fb5114fa596dadd104625ff618cccaf03c787fb49034a793eb57'},
}
CHUNK = 512


def sha(data):
    return hashlib.sha256(data).hexdigest()


def decode_mutant(name, raw, expected_digest):
    r.require(sha(raw) == PINS[name], 'unknown mutant R1CS')
    r.require(raw[:12] == b'r1cs\x01\0\0\0\x05\0\0\0', 'unexpected R1CS header')
    artifact = r.parse_r1cs(raw[:8] + (3).to_bytes(4, 'little') + raw[12:])
    r.require([s['type'] for s in artifact['sections']] == [2, 1, 3], 'wrong section order')
    r.require(r.constraints_digest(artifact['constraints']) == expected_digest,
              'strict Python and archived JS constraint decodings disagree')
    return artifact


def load(name):
    directory = EVIDENCE / name
    result = json.loads((directory / 'result.json').read_text())
    pin = RECORD_PINS[name]
    r.require(result['archive_sha256'] == pin['archive'] and
              result['artifact']['spend.sym']['sha256'] == pin['spend.sym'] and
              result['artifact']['witness.wtns']['sha256'] == pin['witness.wtns'] and
              result['decoded_constraints_sha256'] == pin['decoded'],
              'archived record differs from the owned pins')
    archive = directory / 'artifacts.tar.gz'
    r.require(sha(archive.read_bytes()) == result['archive_sha256'], 'archive hash mismatch')
    with tarfile.open(archive) as t:
        r.require(set(t.getnames()) == {'spend.circom', 'spend.r1cs', 'spend.sym',
                                      'witness.wtns', 'spend.wasm'}, 'unexpected archive members')
        files = {n: t.extractfile(n).read() for n in t.getnames()}
    for filename, expected in result['artifact'].items():
        data = files[filename]
        r.require(len(data) == expected['bytes'] and sha(data) == expected['sha256'],
                  f'{filename}: wrong bytes')
    source_bytes = (ROOT / 'circuits/spend.circom').read_bytes()
    r.require(sha(source_bytes) == r.SOURCE_PIN, 'canonical source pin mismatch')
    source = source_bytes.decode()
    r.require(files['spend.circom'].decode() == m.mutate(source, name), 'wrong source mutation')
    raw = files['spend.r1cs']
    artifact = decode_mutant(name, raw, result['decoded_constraints_sha256'])
    with tempfile.TemporaryDirectory(prefix='msp-mutant-export-') as tmp:
        witness = Path(tmp) / 'witness.wtns'
        witness.write_bytes(files['witness.wtns'])
        values = m.read_wtns(witness)
    r.require(len(values) == artifact['header']['wires'], 'witness length mismatch')
    rows = {}
    for line in files['spend.sym'].decode().splitlines():
        label, wire, component, signal = line.split(',')
        label, wire, component = int(label), int(wire), int(component)
        r.require(signal not in rows, 'duplicate symbol')
        r.require(wire == -1 or (0 <= wire < len(values) and artifact['labels'][wire] == label),
                  'symbol disagrees with R1CS labels')
        rows[signal] = dict(label=label, wire=None if wire == -1 else wire, component=component)
    canonical = json.loads((ROOT / 'formal/Artifacts/spend.manifest.json').read_text())['signals']
    selected = r.selected_symbols(rows)
    r.require(set(selected) == set(canonical), 'different projection names')
    for signal in selected:
        r.require(selected[signal]['wire'] == canonical[signal]['wire'],
                  f'{signal}: cannot reuse the canonical concrete projection')
    return artifact, values, result


def tree(values, references=False):
    if len(values) == 1:
        return values[0] if references else f'(.leaf {values[0]})'
    return f'(.branch {tree(values[::2], references)} {tree(values[1::2], references)})'


def render(name):
    artifact, values, result = load(name)
    title = name.capitalize()
    namespace = f'MSP.Mutations.{title}'
    prefix = f'Mutations.{title}'
    banner = (f'/-! Generated by tools/mutation_certificates.py --write --case {name}.\n'
              f'Raw R1CS SHA256: {PINS[name]}.\n'
              f'WTNS SHA256: {result["artifact"]["witness.wtns"]["sha256"]}.\n'
              'All numerical equations below are checked by the Lean kernel. -/\n')
    options = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n'
    header = banner + f'namespace {namespace}\n' + options
    end = f'end {namespace}\n'
    padded = values + [0] * ((1 << (len(values) - 1).bit_length()) - len(values))
    table = f'import Mutations.Check\n{header}'
    for i in range(64):
        table += f'private def part{i} : WireTable := {tree(padded[i::64])}\n'
    table += f'def table : WireTable := {tree([f"part{i}" for i in range(64)], True)}\n' + end
    output = {f'{title}Table.lean': table}
    constraints = artifact['constraints']
    blocks = []
    for offset in range(0, len(constraints), CHUNK):
        index = offset // CHUNK
        block = f'block{index}'
        blocks.append(block)
        text = f'import {prefix}Table\n{header}def {block} : List Artifacts.Constraint := [\n'
        literals = []
        for c in constraints[offset:offset + CHUNK]:
            sides = ['[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in side) + ']'
                     for side in c]
            literals.append('⟨' + ', '.join(sides) + '⟩')
        text += ',\n'.join(literals) + ']\n'
        text += f'theorem {block}_checked : checkAssignmentConstraints table.toAssignment {block} = true := by decide\n'
        output[f'{title}Chunk{index}.lean'] = text + end
    text = ''.join(f'import {prefix}Chunk{i}\n' for i in range(len(blocks))) + header
    text += f'def system : Artifacts.System := ⟨{len(values)}, [{", ".join(blocks)}].flatten⟩\n'
    text += 'theorem satisfied : system.Satisfied table.toAssignment := by\n'
    text += '  apply satisfied_of_checked_blocks\n  · decide\n  · intro cs hc\n'
    text += '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc\n'
    text += '    rcases hc with ' + ' | '.join(['rfl'] * len(blocks)) + '\n'
    text += ''.join(f'    · exact {block}_checked\n' for block in blocks)
    output[f'{title}Certificate.lean'] = text + end
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=list(PINS), default='membership')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    output = render(args.case)
    for filename, text in output.items():
        path = ROOT / 'formal/Mutations' / filename
        if args.write:
            path.write_text(text)
        else:
            r.require(path.read_text() == text, f'stale generated certificate: {filename}')
    print(f'{args.case}: {len(output)} generated files ' + ('written' if args.write else 'match exactly'))


if __name__ == '__main__':
    main()
