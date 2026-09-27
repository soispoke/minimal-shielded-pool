#!/usr/bin/env python3
"""Export exact affine states and kernel certificates for all 54 small hashes."""

import argparse
from pathlib import Path
import sys

from r1cs_artifact import P, PIN, ROOT, InvalidArtifact, parse_r1cs, require
import small_hash_gates as small
from hash_instances import add, constant, mix, triple_forms

sys.path.insert(0, str(ROOT / 'formal/Poseidon'))
import small_optimized_generate as optimized

DESTINATION = ROOT / 'formal/Artifacts'


def field_form(form):
    return add([(wire, int(coefficient)) for wire, coefficient in form])


def prepare(data, mapping, node_modules):
    records = small.prepare(data, mapping)
    constraints = parse_r1cs(data, pinned_compat=True)['constraints']
    params = {t: optimized.prepare(node_modules, t) for t in (3, 4)}
    result = []
    for index, record in enumerate(records):
        width, rp = record['width'], record['partial_rounds']
        require(width in params and rp == optimized.WIDTHS[width], 'wrong small-hash width/round count')
        C, M, pre, _, sparse, _, _ = params[width]
        stages = record['sigma_constraint_offsets']
        fixed = {int(j): int(value) for j, value in record['constant_folded_first_coordinates'].items()}
        full_in, full_out = [], []
        for r in range(8):
            ins, outs = [], []
            for j in range(width):
                offset = stages[f'sigmaF[{r}][{j}]']
                if offset is None:
                    require(r == 0 and j in fixed, f'instance {index}: unexpected constant fold')
                    x = (fixed[j] + C[j]) % P
                    ins.append(constant(x))
                    outs.append(constant(pow(x, 5, P)))
                else:
                    x, y = triple_forms(constraints, offset)
                    ins.append(x)
                    outs.append(y)
            full_in.append(ins)
            full_out.append(outs)
        inputs = [field_form(form) for form in record['input_forms']]
        require(full_in[0] == [constant(C[0])] +
                [add(form, constant(C[j + 1])) for j, form in enumerate(inputs)],
                f'instance {index}: initial state mismatch')
        for r in range(3):
            expected = mix(M, [add(form, constant(C[width + width*r + j]))
                               for j, form in enumerate(full_out[r])])
            require(full_in[r + 1] == expected, f'instance {index}: prefix {r}')
        state = mix(pre, [add(form, constant(C[4*width + j])) for j, form in enumerate(full_out[3])])
        partial_states = [state]
        for r in range(rp):
            inp, out = triple_forms(constraints, stages[f'sigmaP[{r}]'])
            require(state[0] == inp, f'instance {index}: partial input {r}')
            state = mix(sparse[r], [add(out, constant(C[5*width + r]))] + state[1:])
            partial_states.append(state)
        require(state == full_in[4], f'instance {index}: partial/suffix boundary')
        for r in range(3):
            expected = mix(M, [add(form, constant(C[5*width + rp + width*r + j]))
                               for j, form in enumerate(full_out[4 + r])])
            require(full_in[5 + r] == expected, f'instance {index}: suffix {r}')
        require(mix(M, full_out[7])[0] == field_form(record['output_form']),
                f'instance {index}: final output')
        result.append((record, partial_states))
    return result


def lean_form(form):
    return '[' + ', '.join(f'({wire}, {coefficient})' for wire, coefficient in form) + ']'


def render_data(index, record, states):
    width, rp = record['width'], record['partial_rounds']
    lines = ['import Artifacts.SmallHashGatesSchedule', '',
             f'/-! Exact normalized affine states for {record["name"]}.',
             f'R1CS SHA-256: {PIN}. Inventory SHA-256: {small.MAP_PIN}.',
             'These are witnesses; the corresponding certificate module checks every transition. -/', '',
             'namespace MSP.Artifacts.SmallHashGatesAffineData', '',
             'open BetaGates', '', 'set_option maxRecDepth 65536', '']
    for r, state in enumerate(states):
        lines += [f'def state{index}_{r} : Fin {width} → Form :=',
                  '  ![' + ',\n    '.join(lean_form(form) for form in state) + ']', '']
    lines += [f'def states{index} : Vector (Fin {width} → Form) {rp + 1} :=',
              '  ⟨#[' + ', '.join(f'state{index}_{r}' for r in range(rp + 1)) + '], rfl⟩', '',
              f'def partialStates{index} (r : Fin {rp + 1}) : Fin {width} → Form := states{index}.get r', '',
              'end MSP.Artifacts.SmallHashGatesAffineData', '']
    return '\n'.join(lines)


def render_certificate(index, record):
    scheme = f'scheme{record["width"]}'
    lines = [f'import Artifacts.SmallHashGatesAffineData{index}', '',
             f'/-! Kernel-checked affine schedule for {record["name"]}. -/', '',
             'namespace MSP.Artifacts.SmallHashGatesAffineCertificates', '',
             'open SmallHashGates SmallHashGatesData SmallHashGatesAffineData', '',
             'set_option maxRecDepth 65536', 'set_option maxHeartbeats 0', '',
             f'def affine{index} : AffineCertificates instance{index} {scheme} where',
             f'  partialStates := partialStates{index}']
    for field in ('initial', 'prefixSteps', 'prefixBoundary', 'partialInputs', 'partialSteps',
                  'partialBoundary', 'suffixSteps', 'finalMix'):
        lines += [f'  {field} := by decide']
    lines += ['', 'end MSP.Artifacts.SmallHashGatesAffineCertificates', '']
    return '\n'.join(lines)


def outputs(data, mapping, node_modules):
    prepared = prepare(data, mapping, node_modules)
    result = {}
    for index, (record, states) in enumerate(prepared):
        result[f'SmallHashGatesAffineData{index}.lean'] = render_data(index, record, states).encode()
        result[f'SmallHashGatesAffineCertificates{index}.lean'] = render_certificate(index, record).encode()
    for stem in ('SmallHashGatesAffineData', 'SmallHashGatesAffineCertificates'):
        result[stem + '.lean'] = ('\n'.join(f'import Artifacts.{stem}{i}' for i in range(54)) + '\n').encode()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--node-modules', type=Path, default=ROOT / 'tooling/node_modules')
    args = parser.parse_args()
    data, mapping = (ROOT / 'build/spend.r1cs').read_bytes(), small.MAP.read_bytes()
    result = outputs(data, mapping, args.node_modules)
    for name, expected in result.items():
        destination = DESTINATION / name
        if args.write:
            destination.write_bytes(expected)
        else:
            require(destination.read_bytes() == expected, f'{name} differs from exact regeneration')
    print(f'All 54 affine schedules and {len(result)} Lean source files match the pinned artifacts.')


if __name__ == '__main__':
    try:
        main()
    except (InvalidArtifact, OSError, ValueError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
