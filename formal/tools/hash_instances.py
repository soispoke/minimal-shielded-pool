#!/usr/bin/env python3
"""Inventory remaining optimized note/path hashes from exact R1CS and symbols.

The JSON is an extraction/checking artifact, not a Lean proof of hash semantics.
All affine round connections are checked numerically modulo the pinned field;
these checks prepare the finite certificates still required in Lean.
"""
import argparse
import ast
from collections import defaultdict
import json
from pathlib import Path
import re
import sys
from r1cs_artifact import P, PIN, SOURCE_PIN, SYM_PIN, ROOT, require, sha, parse_r1cs, symbol_rows, reproduce, InvalidArtifact

CONSTANTS_PIN = '94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee'
DESTINATION = ROOT / 'formal/Artifacts/hash-instance-map.json'
INSTANCE_RE = r'main\.spend\.(?:note\[[01]\]\.(?:pk|inner|leaf|domainKey|occurrence|null|node\[\d+\])|outCm\[[01]\])'
SIGMA_RE = re.compile(r'('+INSTANCE_RE+r')\.pEx\.(sigmaF\[\d+\]\[\d+\]|sigmaP\[\d+\])\.in2')


def add(*forms):
    result = defaultdict(int)
    for form in forms:
        for wire, coefficient in form:
            result[wire] = (result[wire]+coefficient) % P
    return sorted((wire,c) for wire,c in result.items() if c)


def scale(c, form):
    return add([(wire,c*coefficient) for wire,coefficient in form])


def constant(c):
    return add([(0,c)])


def mix(matrix, state):
    return [add(*(scale(matrix[j][i],state[j]) for j in range(len(state))))
            for i in range(len(state))]


def extract_constant(source, name, width):
    body = source.split('function POSEIDON_'+name+'(',1)[1]
    match = re.search(r'if\s*\(\s*t\s*==\s*'+str(width)+r'\s*\)\s*\{\s*return\s*',body)
    require(match is not None,f'missing constants {name}/{width}')
    start = body.index('[',match.end())
    depth = 0
    for end in range(start,len(body)):
        depth += (body[end]=='[')-(body[end]==']')
        if depth==0:
            return ast.literal_eval(body[start:end+1])
    raise InvalidArtifact('unterminated constants')


def wire(rows, name):
    value = rows[name]['wire']
    require(value is not None,f'required retained interface signal was eliminated: {name}')
    return [(value,1)]


def triple_forms(constraints, offset):
    c0,c1,c2 = constraints[offset:offset+3]
    require(add(c0[0])==scale(-1,c0[1]),f'square input sign at {offset}')
    require(add(c0[2])==scale(-1,c1[1]),f'square output sign at {offset}')
    require(add(c1[0])==scale(-1,c1[1]),f'fourth input sign at {offset}')
    require(add(c2[0])==add(c1[2]),f'fourth output sign at {offset}')
    require(add(c2[1])==add(c0[1]),f'fifth input reuse at {offset}')
    return add(c0[1]),scale(-1,c2[2])


def analyze(data, sym, source, constants):
    require(sha(data)==PIN,'hash inventory requires exact pinned R1CS')
    require(sha(source)==SOURCE_PIN,'spend circuit source changed')
    require(sha(constants)==CONSTANTS_PIN,'optimized constants changed')
    artifact = parse_r1cs(data,pinned_compat=True)
    rows = symbol_rows(sym,artifact)
    cs = artifact['constraints']
    by_square = defaultdict(list)
    for offset,c in enumerate(cs):
        if len(c[2])==1 and c[2][0][1]==P-1:
            by_square[c[2][0][0]].append(offset)
    stages = defaultdict(dict)
    for name,row in rows.items():
        match = SIGMA_RE.fullmatch(name)
        if not match:
            continue
        instance,stage = match.groups()
        if row['wire'] is None:
            stages[instance][stage] = None
        else:
            offsets = by_square[row['wire']]
            require(len(offsets)==1,f'ambiguous square anchor {name}')
            stages[instance][stage] = offsets[0]
    expected_names = {f'main.spend.note[{k}].{part}' for k in range(2)
                      for part in ['pk','inner','leaf','domainKey','occurrence','null']+[f'node[{i}]' for i in range(20)]}
    expected_names |= {f'main.spend.outCm[{k}]' for k in range(2)}
    require(set(stages)==expected_names,'hash instance set changed')
    parameters = {}
    for width,partial_rounds in [(3,57),(4,56)]:
        C,M,pre,S=[extract_constant(constants.decode(),name,width) for name in ['C','M','P','S']]
        require(len(C)==8*width+partial_rounds,'round constant dimension')
        require(len(S)==partial_rounds*(2*width-1),'sparse coefficient dimension')
        require(len(M)==len(pre)==width and all(len(row)==width for m in [M,pre] for row in m),
                'matrix dimension')
        parameters[width]=(partial_rounds,C,M,pre,S)
    records=[]
    for name,stage_map in stages.items():
        role=name.rsplit('.',1)[1]
        width=4 if role in ['pk','leaf','null'] or role.startswith('outCm') else 3
        rp,C,M,pre,S=parameters[width]
        expected_stages={f'sigmaF[{r}][{i}]' for r in range(8) for i in range(width)}
        expected_stages|={f'sigmaP[{r}]' for r in range(rp)}
        require(set(stage_map)==expected_stages,f'stage set for {name}')
        # Source-fixed coordinates that the compiler entirely constant-folded.
        fixed={0:0}
        if role=='pk':fixed.update({1:1,3:0})
        elif role=='leaf' or role.startswith('outCm'):fixed[1]=2
        elif role=='null':fixed[1]=4
        require({s for s,o in stage_map.items() if o is None}==
                {f'sigmaF[0][{i}]' for i in fixed},f'unexpected elimination at {name}')
        full_in,full_out=[],[]
        for r in range(8):
            ins,outs=[],[]
            for i in range(width):
                offset=stage_map[f'sigmaF[{r}][{i}]']
                if offset is None:
                    x=(fixed[i]+C[i])%P
                    ins.append(constant(x)); outs.append(constant(pow(x,5,P)))
                else:
                    x,y=triple_forms(cs,offset)
                    ins.append(x); outs.append(y)
            full_in.append(ins); full_out.append(outs)
        for r in range(3):
            require(full_in[r+1]==mix(M,[add(f,constant(C[(r+1)*width+i])) for i,f in enumerate(full_out[r])]),
                    f'prefix affine mismatch {name}/{r}')
        state=mix(pre,[add(f,constant(C[4*width+i])) for i,f in enumerate(full_out[3])])
        for r in range(rp):
            inp,out=triple_forms(cs,stage_map[f'sigmaP[{r}]'])
            require(state[0]==inp,f'partial input mismatch {name}/{r}')
            state=[add(out,constant(C[5*width+r]))]+state[1:]
            s=S[(2*width-1)*r:(2*width-1)*(r+1)]
            state=[add(*(scale(s[i],state[i]) for i in range(width)))]+[
                add(state[i],scale(s[width+i-1],state[0])) for i in range(1,width)]
        require(state==full_in[4],f'partial/suffix affine mismatch {name}')
        for r in range(3):
            require(full_in[5+r]==mix(M,[add(f,constant(C[5*width+rp+r*width+i]))
                                       for i,f in enumerate(full_out[4+r])]),f'suffix affine mismatch {name}/{r}')
        inputs=[add(full_in[0][i],constant(-C[i])) for i in range(1,width)]
        output=mix(M,full_out[7])[0]
        offsets=sorted(o for o in stage_map.values() if o is not None)
        require(offsets==list(range(offsets[0],offsets[-1]+1,3)),f'noncontiguous instance {name}')
        records.append({'name':name,'arity':width-1,'width':width,'partial_rounds':rp,
            'constraint_start':offsets[0],'constraint_end_exclusive':offsets[-1]+3,
            'sbox_triples':len(offsets),'constant_folded_first_coordinates':fixed,
            'symbol_inputs':[rows[f'{name}.inputs[{i}]']['wire'] for i in range(width-1)],
            'symbol_output':rows[f'{name}.out']['wire'],
            'input_forms':inputs,'output_form':output,
            'sigma_constraint_offsets':stage_map})
    records.sort(key=lambda rec:rec['constraint_start'])
    require(all(a['constraint_end_exclusive'] <= b['constraint_start']
                for a,b in zip(records,records[1:])), 'overlapping hash constraint intervals')
    outputs={rec['name']:rec['output_form'] for rec in records}
    for rec in records:
        name=rec['name'];role=name.rsplit('.',1)[1]
        k=int(re.search(r'\[(\d+)\]',name).group(1))
        base=f'main.spend.note[{k}].'
        out=None
        if role=='pk':
            expected=[constant(1),wire(rows,f'main.in_spend_key[{k}]'),[]]
            out=wire(rows,base+'inner.inputs[0]')
        elif role=='inner':
            expected=[outputs[base+'pk'],wire(rows,f'main.in_rho[{k}]')]
            out=wire(rows,base+'inner.out')
        elif role=='leaf':
            expected=[constant(2),outputs[base+'inner'],wire(rows,f'main.in_value[{k}]')]
            out=wire(rows,base+'cur[0]')
        elif role=='domainKey':
            expected=[wire(rows,'main.domain'),wire(rows,f'main.in_spend_key[{k}]')]
            out=wire(rows,base+'domainKey.out')
        elif role=='occurrence':
            index=add(*(scale(2**i,wire(rows,f'main.in_bits[{k}][{i}]')) for i in range(20)))
            expected=[outputs[base+'leaf'],index]
        elif role=='null':
            expected=[constant(4),outputs[base+'domainKey'],outputs[base+'occurrence']]
            out=wire(rows,f'main.stmt[{k}]')
        elif role.startswith('node'):
            i=int(re.search(r'\[(\d+)\]',role).group(1))
            expected=[wire(rows,base+f'left[{i}]'),wire(rows,base+f'right[{i}]')]
            out=wire(rows,base+f'cur[{i+1}]')
        else:
            expected=[constant(2),wire(rows,f'main.out_inner[{k}]'),wire(rows,f'main.out_value[{k}]')]
            out=wire(rows,f'main.stmt[{2+k}]')
        require(rec['input_forms']==expected,f'source interface inputs mismatch {name}')
        if out is not None:
            require(rec['output_form']==out,f'source interface output mismatch {name}')
        # Keep large field coefficients lossless for JSON/JavaScript readers.
        rec['input_forms']=[[[w,str(c)] for w,c in f] for f in rec['input_forms']]
        rec['output_form']=[[w,str(c)] for w,c in rec['output_form']]
    return {'schema':1,'r1cs_sha256':PIN,'symbols_sha256':SYM_PIN,'circuit_source_sha256':SOURCE_PIN,
        'optimized_constants_sha256':CONSTANTS_PIN,'field_modulus':str(P),
        'scope':'Remaining 54 note/path/output hashes only; beta is separate.',
        'status':'Extracted and numerically checked affine interfaces; not a Lean hash proof or C1.',
        'form_encoding':'[wire, decimal coefficient] pairs modulo field; wire0=1 is the constant wire.',
        'checks':['unique retained sigma.in2 anchors','all local three-equation S-box shapes',
                  'all prefix/partial/suffix/final affine connections','source input/output interface forms'],
        'remaining':['kernel-check width3/4 optimized/reference equivalence',
                     'export and kernel-check instance coefficient certificates and full-system containment',
                     'connect resulting hash equations to RelationFragments.relation_of_gadget_hashes'],
        'instances':records}


def render(data,sym,source,constants):
    return (json.dumps(analyze(data,sym,source,constants),indent=2,sort_keys=True)+'\n').encode()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--node-modules',type=Path,required=True)
    symbols=parser.add_mutually_exclusive_group(required=True)
    symbols.add_argument('--sym',type=Path)
    symbols.add_argument('--reproduce',action='store_true')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    data=(ROOT/'build/spend.r1cs').read_bytes()
    if args.sym:
        sym=args.sym.read_bytes()
    else:
        data2,_,rows=reproduce(args.node_modules)
        require(data2==data,'recompiled R1CS differs')
        sym=''.join(f'{r["label"]},{-1 if r["wire"] is None else r["wire"]},{r["component"]},{n}\n'
                    for n,r in sorted(rows.items(),key=lambda v:v[1]['label'])).encode()
    expected=render(data,sym,(ROOT/'circuits/spend.circom').read_bytes(),
                    (args.node_modules/'circomlib/circuits/poseidon_constants.circom').read_bytes())
    if args.write:DESTINATION.write_bytes(expected)
    else:require(DESTINATION.read_bytes()==expected,'hash instance map differs from extraction')
    print('Mapped 54 hash instances; exact pins, S-box triples, affine schedules, and source interfaces checked.')


if __name__=='__main__':
    try:main()
    except (InvalidArtifact,OSError,ValueError,KeyError) as error:
        print(f'ERROR: {error}',file=sys.stderr);sys.exit(1)
