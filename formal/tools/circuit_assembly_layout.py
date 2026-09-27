#!/usr/bin/env python3
"""Generate exact assembly write/read certificates from the frozen circuit plan."""
import argparse
import json
import sys
from r1cs_artifact import PIN, ROOT, InvalidArtifact, parse_r1cs, require, sha
from small_hash_gates import MAP, MAP_PIN

PLAN = ROOT/'formal/Artifacts/assignment-plan.json'
PLAN_PIN = '73eeee9fcb7b6651c1df319d019592f9e0dd5c35d9a5d4941539dd40b065fc7a'
DEST = ROOT/'formal/Artifacts'


def compress(wires):
    spans=[]
    for wire in sorted(wires):
        if spans and spans[-1][1] == wire:
            spans[-1][1] += 1
        else:
            spans.append([wire,wire+1])
    return spans


def boundary(w):
    return w<103 or 730<=w<792 or 7060<=w<7122 or w in (1031,1032,7361,7362,6309,12639)


def prepare(data, plan_data, map_data):
    require(sha(data)==PIN,'R1CS pin changed')
    require(sha(plan_data)==PLAN_PIN,'assignment plan pin changed')
    require(sha(map_data)==MAP_PIN,'hash inventory pin changed')
    plan=json.loads(plan_data)
    blocks=plan['hash_blocks']
    require(len(blocks)==55,'expected 55 hashes')
    ownership=[]
    outputs=[]
    ranges=[]
    for b in blocks:
        affine={w for lo,hi in b['affine_wire_intervals'] for w in range(lo,hi)}
        powers=b['square_wires']+b['fourth_wires']
        require(len(set(powers))==len(powers),'overlapping powers')
        require(not affine.intersection(powers),'affine and power overlap')
        ownership.append(affine|set(powers))
        require(len(b['output_form'])==1 and int(b['output_form'][0][1])==1,'output is not one wire')
        outputs.append(b['output_form'][0][0])
        lo,hi=b['constraint_interval'];ranges.append(list(range(lo,hi)))
    ownership += [set(range(569,728))|set(range(13918,14839)),
                  {728,729,*range(13904,13918),14839,14840,14841},set(range(103,111)),set()]
    ranges += [list(range(474,634))+list(range(13870,14798)),
               list(range(468,474))+list(range(634,636))+list(range(13856,13870))+list(range(14798,14802)),
               list(range(9)),list(range(636,697))+list(range(6988,7049))]
    validate(ownership,outputs,ranges,parse_r1cs(data,pinned_compat=True)['constraints'])
    return [compress(s) for s in ownership],outputs


def validate(ownership,outputs,ranges,constraints):
    require(len(ownership)==len(ranges)==59,'wrong part count')
    written=set()
    for i,wires in enumerate(ownership):
        require(not written.intersection(wires),'component write sets overlap')
        written.update(wires)
        if i<55:
            require({w for w in wires if boundary(w)}=={outputs[i]},'hash boundary intersection is not its output')
        else:
            require(not any(boundary(w) for w in wires),'nonhash writes intersect boundary')
        for c in ranges[i]:
            for side in constraints[c]:
                for wire,_ in side:
                    require(wire in wires or boundary(wire),f'unsupported read in part {i}, constraint {c}, wire {wire}')


def render_core(spans,outputs):
    fmt=lambda ss:'['+', '.join(f'({lo}, {hi})' for lo,hi in ss)+']'
    lines=['import Artifacts.ConstraintCoverage','import Artifacts.AssignmentAssembly','','/-! Exact physical layout of the 59 independently assembled circuit parts.',
           f'Generated from assignment plan SHA-256 `{PLAN_PIN}`.',
           'All write intervals include both retained powers and recovered affine outputs. -/','',
           'namespace MSP.Artifacts.CircuitAssemblyLayout','',
           '/-- Canonical shared source, selector, path-state and hash-output wires. -/',
           'def boundary (wire : ℕ) : Prop :=',
           '  wire < 103 ∨ (730 ≤ wire ∧ wire < 792) ∨ (7060 ≤ wire ∧ wire < 7122) ∨',
           '  wire = 1031 ∨ wire = 1032 ∨ wire = 7361 ∨ wire = 7362 ∨ wire = 6309 ∨ wire = 12639','',
           'instance (wire : ℕ) : Decidable (boundary wire) := by unfold boundary; infer_instance','',
           'def spanData : Vector (List (ℕ × ℕ)) 59 :=',
           '  ⟨#['+',\n    '.join(fmt(ss) for ss in spans)+'], rfl⟩','',
           'def spans (i : Fin 59) : List (ℕ × ℕ) := spanData.get i','',
           'def writes (i : Fin 59) (wire : ℕ) : Prop :=',
           '  ∃ span ∈ spans i, span.1 ≤ wire ∧ wire < span.2','',
           'instance (i : Fin 59) (wire : ℕ) : Decidable (writes i wire) := by',
           '  unfold writes', '  infer_instance','',
           'def smallPart (i : Fin 54) : Fin 59 := ⟨i.val + 1, by omega⟩','',
           'def familyData : Vector ConstraintCoverage.Family 59 :=',
           '  ⟨#[.beta, '+', '.join(f'.small {i}' for i in range(54))+', .ranges, .controls, .gamma, .paths], rfl⟩','',
           'def constraints (i : Fin 59) : List Constraint := (familyData.get i).constraints','',
           'def outputData : Vector ℕ 55 := ⟨#['+', '.join(map(str,outputs))+'], rfl⟩',
           'def outputWire (i : Fin 55) : ℕ := outputData.get i','',
           'theorem constraints_small (i : Fin 54) :',
           '    constraints (smallPart i) = (SmallHashGatesData.gate i).constraints := by',
           '  fin_cases i <;> rfl','',
           'theorem source_boundary (wire : ℕ) (h : wire < 103) : boundary wire := Or.inl h','',
           'end MSP.Artifacts.CircuitAssemblyLayout','']
    return '\n'.join(lines)


def render_support(i):
    return f'''import Artifacts.CircuitAssemblyLayout

namespace MSP.Artifacts.CircuitAssemblyLayout
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

/-- Every actual coefficient wire of part {i} is owned or shared. -/
theorem supported{i} : ∀ c ∈ constraints {i}, AssignmentAssembly.Supported (writes {i}) boundary c := by
  unfold AssignmentAssembly.Supported
  decide

end MSP.Artifacts.CircuitAssemblyLayout
'''


def render_aggregate():
    s='\n'.join(f'import Artifacts.CircuitAssemblyLayoutSupport{i}' for i in range(59))+'\n\n'
    s+='namespace MSP.Artifacts.CircuitAssemblyLayout\n\n'
    s+='theorem supported (i : Fin 59) : ∀ c ∈ constraints i, AssignmentAssembly.Supported (writes i) boundary c := by\n  fin_cases i\n'
    s+=''.join(f'  · exact supported{i}\n' for i in range(59))
    s+='\n#print axioms supported\n\nend MSP.Artifacts.CircuitAssemblyLayout\n'
    return s


def exports(data,plan_data,map_data):
    spans,outputs=prepare(data,plan_data,map_data)
    result={DEST/'CircuitAssemblyLayout.lean':render_core(spans,outputs),
            DEST/'CircuitAssemblyLayoutSupport.lean':render_aggregate()}
    result.update({DEST/f'CircuitAssemblyLayoutSupport{i}.lean':render_support(i) for i in range(59)})
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');args=parser.parse_args()
    generated=exports((ROOT/'build/spend.r1cs').read_bytes(),PLAN.read_bytes(),MAP.read_bytes())
    for file,text in generated.items():
        if args.write:file.write_text(text)
        else:require(file.read_text()==text,f'{file.name} regeneration mismatch')
    print('59 exact write sets are disjoint; every actual coefficient read is owned or boundary; only55 hash outputs intersect boundary.')

if __name__=='__main__':
    try:main()
    except (InvalidArtifact,OSError,ValueError,KeyError) as error:
        print(f'ERROR: {error}',file=sys.stderr);sys.exit(1)
