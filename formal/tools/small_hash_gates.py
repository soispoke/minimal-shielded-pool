#!/usr/bin/env python3
"""Export typed slices and kernel-checkable S-box certificates for the 54 small hashes."""
import argparse
import json
import sys
from r1cs_artifact import P, PIN, ROOT, SOURCE_PIN, SYM_PIN, InvalidArtifact, parse_r1cs, require, sha
from hash_instances import triple_forms, CONSTANTS_PIN

MAP = ROOT / 'formal/Artifacts/hash-instance-map.json'
MAP_PIN = '6f90e7cd87fb9a3c473d83f665cefd3392ba6363d1f96eb92baf133a10f09368'
DESTINATION = ROOT / 'formal/Artifacts/SmallHashGatesData.lean'
CERTIFICATES = ROOT / 'formal/Artifacts/SmallHashGatesCertificates.lean'


def prepare(data, mapping):
    require(sha(data) == PIN, 'small hash gates require exact pinned R1CS')
    require(sha(mapping) == MAP_PIN, 'small hash instance map changed')
    inventory = json.loads(mapping)
    for field, value in [('r1cs_sha256', PIN), ('symbols_sha256', SYM_PIN),
                         ('circuit_source_sha256', SOURCE_PIN),
                         ('optimized_constants_sha256', CONSTANTS_PIN), ('field_modulus', str(P))]:
        require(inventory[field] == value, f'wrong inventory pin: {field}')
    records = inventory['instances']
    require(len(records) == 54, 'wrong instance count')
    constraints = parse_r1cs(data, pinned_compat=True)['constraints']
    for record in records:
        start, end, count = (record[k] for k in ['constraint_start', 'constraint_end_exclusive', 'sbox_triples'])
        offsets = sorted(o for o in record['sigma_constraint_offsets'].values() if o is not None)
        require(end-start == 3*count and offsets == list(range(start, end, 3)), 'invalid instance slice')
        for offset in offsets:
            triple_forms(constraints, offset)
    require(sum(r['sbox_triples'] for r in records) == 4366, 'wrong total retained S-box count')
    return records


def form(terms):
    return '[' + ', '.join(f'({wire}, {int(coefficient)})' for wire, coefficient in terms) + ']'


def vector(items):
    return '![' + ', '.join(items) + ']'


def render(data, mapping):
    records = prepare(data, mapping)
    lines = ['import Artifacts.SmallHashGatesLemmas', '', '/-!', '# Typed actual small-hash instances', '',
             f'R1CS SHA-256 `{PIN}`.', f'Inventory SHA-256 `{MAP_PIN}`.',
             'Generated with `python3 formal/tools/small_hash_gates.py --write`.',
             'Every slice has a kernel-checked membership proof in the full Spend system.',
             'Input/output interface forms are data; their full affine bindings remain separate.',
             '-/', '', 'namespace MSP.Artifacts.SmallHashGatesData', '',
             'open SmallHashGates BetaGates', '', 'set_option maxRecDepth 65536', '']
    for k, record in enumerate(records):
        start, end, count = (record[key] for key in ['constraint_start', 'constraint_end_exclusive', 'sbox_triples'])
        groups = list(range(start//256, (end-1)//256 + 1))
        lines += [f'/-- {record["name"]}, constraints {start}..{end-1}. -/',
                  f'def slice{k} : List Constraint :=',
                  '  ([' + ', '.join(f'Spend.group{g}' for g in groups) + f'].flatten.drop {start%256}).take {end-start}', '',
                  f'private theorem slice{k}_mem {{c : Constraint}} (hc : c ∈ slice{k}) :',
                  '    c ∈ Spend.system.constraints := by',
                  f'  unfold slice{k} at hc',
                  '  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp',
                  '    (List.mem_of_mem_drop (List.mem_of_mem_take hc))',
                  '  apply List.mem_flatten.mpr', '  refine ⟨group, ?_, hm⟩',
                  '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg',
                  '  rcases hg with ' + ' | '.join('rfl' for _ in groups), '  all_goals simp', '',
                  f'def instance{k} : Instance where', f'  name := {json.dumps(record["name"])}',
                  f'  arity := {record["arity"]}', f'  partialRounds := {record["partial_rounds"]}',
                  f'  tripleCount := {count}', f'  constraints := slice{k}',
                  '  constraintCount := rfl', f'  contains := fun _ hc => slice{k}_mem hc']
        full = []
        for r in range(8):
            row = []
            for j in range(record['width']):
                offset = record['sigma_constraint_offsets'][f'sigmaF[{r}][{j}]']
                row.append('none' if offset is None else f'some ⟨{(offset-start)//3}, by decide⟩')
            full.append(vector(row))
        partial = [f'⟨{(record["sigma_constraint_offsets"][f"sigmaP[{r}]"]-start)//3}, by decide⟩'
                   for r in range(record['partial_rounds'])]
        fixed = record['constant_folded_first_coordinates']
        folded = ['none' if str(j) not in fixed else f'some {fixed[str(j)]}' for j in range(record['width'])]
        lines += ['  fullStage := ' + vector(full), '  partialStage := ' + vector(partial),
                  '  foldedInput := ' + vector(folded),
                  '  inputForms := ' + vector([form(f) for f in record['input_forms']]),
                  '  outputForm := ' + form(record['output_form']), '']
    lines += ['def instances : Vector Instance 54 :=',
              '  ⟨#[' + ', '.join(f'instance{i}' for i in range(54)) + '], rfl⟩', '',
              'def gate (i : Fin 54) : Instance := instances.get i', '',
              'end MSP.Artifacts.SmallHashGatesData', '']
    return '\n'.join(lines)


def render_certificates():
    lines = ['import Artifacts.SmallHashGatesData', '',
             '/-! Kernel-checked sign/reuse certificates for all 4,366 retained S-box triples. -/', '',
             'namespace MSP.Artifacts.SmallHashGatesCertificates', '',
             'open SmallHashGates SmallHashGatesData', '',
             'set_option maxRecDepth 65536', 'set_option maxHeartbeats 0', '']
    for i in range(54):
        lines += [f'private theorem signs{i} : ∀ t, TripleSigns instance{i} t := by',
                  '  unfold TripleSigns', '  decide', '']
    lines += ['theorem signs (i : Fin 54) : ∀ t, TripleSigns (gate i) t := by', '  fin_cases i']
    lines += [f'  · exact signs{i}' for i in range(54)]
    lines += ['', '#print axioms signs', '', 'end MSP.Artifacts.SmallHashGatesCertificates', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data, mapping = (ROOT / 'build/spend.r1cs').read_bytes(), MAP.read_bytes()
    for destination, expected in [(DESTINATION, render(data, mapping)), (CERTIFICATES, render_certificates())]:
        if args.write:
            destination.write_text(expected)
        else:
            require(destination.read_text() == expected, f'{destination.name} differs from exact regeneration')
    print('54 typed instances and 4,366 S-box certificates match the exact R1CS and inventory.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
