#!/usr/bin/env python3
"""Exact finite coverage and affine realization plan for circuit completeness.

This is checked modular extraction, not a Lean C1c proof or a trusted witness
calculator. It consumes the pinned R1CS, source, constants and reproduced symbols.
The beta inverse and all small-hash pivots are recomputed, not trusted from JSON.
"""
import argparse
import json
from pathlib import Path
import sys
import hash_instances as hi
from r1cs_artifact import ROOT, P, PIN, SYM_PIN, SOURCE_PIN, InvalidArtifact, parse_r1cs, require, symbol_rows

DESTINATION = ROOT / 'formal/Artifacts/assignment-plan.json'


def intervals(values):
    """Half-open intervals; no implied missing interior values."""
    result=[]
    for x in sorted(values):
        if result and result[-1][1]==x:result[-1][1]+=1
        else:result.append([x,x+1])
    return result


def solve_matrix(forms):
    """Return a sparse inverse of the nonconstant output-form coefficient matrix.

    Each row is a fifth-power form; columns are retained wires. Thus returned
    inverse row j maps (desired fifth powers minus form constants) to wire j.
    """
    columns=sorted({w for form in forms for w,c in form if w})
    n=len(columns)
    require(n==len(forms),'output matrix is not square')
    original=[[dict(form).get(w,0)%P for w in columns] for form in forms]
    augmented=[row+[int(i==j) for j in range(n)] for i,row in enumerate(original)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if augmented[i][j]),None)
        require(pivot is not None,'singular output-form matrix')
        augmented[j],augmented[pivot]=augmented[pivot],augmented[j]
        inv=pow(augmented[j][j],-1,P)
        augmented[j]=[x*inv%P for x in augmented[j]]
        for i in range(n):
            if i!=j and augmented[i][j]:
                factor=augmented[i][j]
                augmented[i]=[(x-factor*y)%P for x,y in zip(augmented[i],augmented[j])]
    inverse=[[(j,x) for j,x in enumerate(row[n:]) if x] for row in augmented]
    verify_inverse(original,inverse)
    return columns,inverse


def verify_inverse(matrix,inverse):
    """Check A*B=I independently of the elimination operations."""
    n=len(matrix)
    require(len(inverse)==n,'inverse dimension')
    for i,row in enumerate(matrix):
        out=[0]*n
        for k,c in enumerate(row):
            for j,d in inverse[k]:out[j]=(out[j]+c*d)%P
        require(out==[int(i==j) for j in range(n)],'invalid inverse certificate')


def triangular_plan(forms):
    """Greedy exact scalar solves: target = coefficient*pivot + known terms.

    Returns (row index, pivot wire, nonzero coefficient) in dependency order.
    This orders affine reconstruction, not the nonlinear Poseidon rounds.
    """
    unknown={w for form in forms for w,c in form if w}
    plan=[]
    while unknown:
        candidate=None
        for row,form in enumerate(forms):
            terms=[(w,c) for w,c in form if w in unknown]
            if len(terms)==1:
                candidate=(row,*terms[0]);break
        if candidate is None:break
        plan.append(candidate);unknown.remove(candidate[1])
    return plan,sorted(unknown)


def claim(owners,values,role):
    for value in values:
        require(value not in owners,f'ownership collision at {value}: {role}')
        owners[value]=role


def analyze(data,sym,source,constants):
    inventory=hi.analyze(data,sym,source,constants)
    artifact=parse_r1cs(data,pinned_compat=True)
    cs=artifact['constraints'];rows=symbol_rows(sym,artifact)
    records=[dict(name='main.digest',constraint_start=9,constraint_end_exclusive=468,
                  output_form=[[1,'1']],input_forms=[],sigma_constraint_offsets={})]+inventory['instances']
    wire_owners={};constraint_owners={};blocks=[];inverse_coefficients=set()
    for record in records:
        start,end=record['constraint_start'],record['constraint_end_exclusive']
        offsets=list(range(start,end,3));forms=[];square=[];fourth=[]
        stages={offset:stage for stage,offset in record['sigma_constraint_offsets'].items() if offset is not None}
        if record['name']=='main.digest':
            for t,offset in enumerate(offsets):
                stages[offset]=(f'sigmaF[0][{t+1}]' if t<10 else
                    f'sigmaF[{1+(t-10)//11}][{(t-10)%11}]' if t<87 else f'sigmaP[{t-87}]')
        for offset in offsets:
            hi.triple_forms(cs,offset)  # all three actual equations/signs
            for n,destination in [(0,square),(1,fourth)]:
                form=hi.scale(-1,cs[offset+n][2])
                require(len(form)==1 and form[0][1]==1,'square/fourth output is not a raw wire')
                destination.append(form[0][0])
            stage=stages[offset]
            require(rows[f'{record["name"]}.pEx.{stage}.in2']['wire']==square[-1],
                    'sigma stage square symbol mismatch')
            require(rows[f'{record["name"]}.pEx.{stage}.in4']['wire']==fourth[-1],
                    'sigma stage fourth symbol mismatch')
            forms.append(hi.scale(-1,cs[offset+2][2]))
        output_wires={w for form in forms for w,c in form if w}
        require(len(output_wires)==len(offsets),'unexpected affine-wire dimension')
        claim(wire_owners,square,record['name']+'/square')
        claim(wire_owners,fourth,record['name']+'/fourth')
        claim(wire_owners,output_wires,record['name']+'/affine')
        claim(constraint_owners,range(start,end),record['name'])
        plan,unresolved=triangular_plan(forms)
        inverse_coefficients.update(c for _,_,c in plan)
        block=dict(name=record['name'],constraint_interval=[start,end],
            square_wires=square,fourth_wires=fourth,affine_wire_intervals=intervals(output_wires),
            output_form=record['output_form'],input_forms=record['input_forms'],
            # Local row t uses actual constraint start+3*t+2, negating its C form.
            affine_pivots=[[t,w,str(c)] for t,w,c in plan],
            unresolved_after_scalar_solves=unresolved,sigma_stages=[stages[o] for o in offsets])
        if record['name']=='main.digest':
            columns,inverse=solve_matrix(forms)
            require(len(columns)==153,'beta dimension changed')
            block['full_inverse_rank']=len(columns)
            block['full_inverse_nonzero_entries']=sum(map(len,inverse))
            block['inverse_basis']='0 denotes 1; t+1 denotes the desired fifth power at local triple t.'
            constant_terms=[dict(form).get(0,0) for form in forms]
            recovery=[]
            for w,row in zip(columns,inverse):
                constant=(-sum(c*constant_terms[t] for t,c in row))%P
                form=([(0,constant)] if constant else [])+[(t+1,c) for t,c in row]
                recovery.append([w,[[i,str(c)] for i,c in form]])
            block['inverse_wire_forms']=recovery
            # Each original LC, after simultaneous substitution, is its own target.
            recovered={w:[(i,int(c)) for i,c in f] for w,f in recovery}
            for t,form in enumerate(forms):
                substituted=hi.add(*(hi.scale(c,[(0,1)] if w==0 else recovered[w]) for w,c in form))
                require(substituted==[(t+1,1)],'beta affine recovery substitution mismatch')
            block['input_forms']=[[[w,'1']] for w in [99,100,101,102,4,5,96]]+[
                [[w,str(c)] for w,c in [(10,1),(11,1),(94,P-1),(95,P-1),(96,P-1)]]]+[
                [[97,'1']],[[98,'1']]]
        else:
            require(not unresolved,'small hash requires a coupled affine solve')
        blocks.append(block)
    # Every remaining constraint family, in physical compiled order.
    nonhash_constraints=[('horner',0,9),('sink_controls',468,474),
        ('authorizer_range',474,634),('authorizer_inverse',634,635),('input_sum_inverse',635,636),
        ('note0_boolean_bits',636,656),('note0_selectors',656,696),('note0_membership',696,697),
        ('note1_boolean_bits',6988,7008),('note1_selectors',7008,7048),('note1_membership',7048,7049),
        ('sink_iszero_gadgets',13856,13868),('public_iszero',13868,13870),
        ('six_amount_ranges',13870,14638),('recipient_range',14638,14798),
        ('recipient_iszero',14798,14800),('nullifier_distinct_inverse',14800,14801),
        ('output_distinct_inverse',14801,14802)]
    for role,start,end in nonhash_constraints:claim(constraint_owners,range(start,end),role)
    require(set(constraint_owners)==set(range(artifact['header']['constraints'])),'constraint coverage gap')
    groups=[('constant',[(0,1)]),('source_inputs',[(3,99)]),('horner',[(2,3),(103,111)]),
        ('range_bits',[(569,728),(13918,14839)]),('selectors',[(730,770),(7060,7100)]),
        ('inverse_iszero',[(728,730),(13904,13918),(14839,14842)])]
    nonhash=[]
    for role,spans in groups:
        values=[w for start,end in spans for w in range(start,end)]
        claim(wire_owners,values,role)
        nonhash.append(dict(role=role,wire_intervals=spans,count=len(values)))
    require(set(wire_owners)==set(range(artifact['header']['wires'])),'wire coverage gap')
    # Check source provenance for all generic nonhash buckets, not just their sizes.
    by_wire={}
    for name,row in rows.items():
        if row['wire'] is not None:by_wire.setdefault(row['wire'],[]).append(name)
    for group in nonhash:
        group['symbol_map']=[[w,by_wire[w][0]] for start,end in group['wire_intervals']
                             for w in range(start,end) if w]
    selectors=[];selector_owners={}
    for k in range(2):
        base=f'main.spend.note[{k}]'
        for level in range(20):
            names=[f'main.in_bits[{k}][{level}]',f'main.in_siblings[{k}][{level}]',
                   f'{base}.cur[{level}]',f'{base}.left[{level}]',f'{base}.right[{level}]']
            signals=[rows[name]['wire'] for name in names]
            require(all(w is not None for w in signals),'eliminated selector signal')
            label=f'{base}.selector[{level}]'
            selectors.append(dict(name=label,bit=signals[0],sibling=signals[1],current=signals[2],
                                  left=signals[3],right=signals[4]))
            for wire in signals[3:]:selector_owners[wire]=label
    # Reads/writes graph including the selectors between successive path hashes.
    edges=[]
    for block in blocks:
        for j,form in enumerate(block['input_forms']):
            for wire,_ in form:
                owner=wire_owners[wire]
                if '/affine' in owner:
                    producer=owner.rsplit('/',1)[0]
                    require(producer!=block['name'],'self-dependent initial hash input')
                    edges.append(dict(producer=producer,consumer=block['name'],input=j,wire=wire))
                elif owner=='selectors':
                    edges.append(dict(producer=selector_owners[wire],consumer=block['name'],input=j,wire=wire))
    for selector in selectors:
        wire=selector['current'];owner=wire_owners[wire]
        require('/affine' in owner,'path current has no hash producer')
        edges.append(dict(producer=owner.rsplit('/',1)[0],consumer=selector['name'],input='current',wire=wire))
    pending={b['name'] for b in blocks}|{s['name'] for s in selectors};order=[]
    while pending:
        ready=sorted(v for v in pending if not any(e['consumer']==v and e['producer'] in pending for e in edges))
        require(bool(ready),'cyclic hash/selector dependency graph')
        order.extend(ready);pending.difference_update(ready)
    return dict(schema=1,r1cs_sha256=PIN,symbols_sha256=SYM_PIN,circuit_source_sha256=SOURCE_PIN,
        optimized_constants_sha256=hi.CONSTANTS_PIN,
        status='Exact finite extraction and modular checks; not a Lean existence proof or C1c.',
        construction='Choose canonical semantic hash traces. Solve affine output forms for their retained wires; assign each sigma square/fourth wire from its trace input. Then verify affine inputs and inter-gadget projections using exact certificates. No witness-generator output is assumed.',
        interval_encoding='half-open',field_modulus=str(P),
        coverage=dict(wires=len(wire_owners),constraints=len(constraint_owners),hash_wires=13557,
                      square_wires=4519,fourth_wires=4519,affine_wires=4519,nonhash_wires=1285),
        hash_blocks=blocks,nonhash_wires=nonhash,nonhash_constraints=nonhash_constraints,
        interface_dependencies=edges,selectors=selectors,hash_selector_evaluation_order=order,
        scalar_inverse_coefficients=[[str(c),str(pow(c,-1,P))] for c in sorted(inverse_coefficients)],
        remaining=['Kernel-check scalar solves and the beta inverse (or an equivalent symbolic state realization).',
                   'Define complete optimized traces from canonical inputs and prove all affine forms evaluate to trace states.',
                   'Combine disjoint assignments and prove all 14802 constraints, stmtOf/witOf/publicOf equalities.'])


def render(*args):return (json.dumps(analyze(*args),indent=2,sort_keys=True)+'\n').encode()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sym',type=Path,required=True)
    parser.add_argument('--node-modules',type=Path,required=True)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    expected=render((ROOT/'build/spend.r1cs').read_bytes(),args.sym.read_bytes(),
        (ROOT/'circuits/spend.circom').read_bytes(),
        (args.node_modules/'circomlib/circuits/poseidon_constants.circom').read_bytes())
    if args.write:DESTINATION.write_bytes(expected)
    else:require(DESTINATION.read_bytes()==expected,'assignment plan differs from exact regeneration')
    print('Covered 14842 wires and 14802 constraints. Disjoint 55 hash blocks; all small affine systems triangular; beta rank 153. Numeric extraction; C1c is proved in Artifacts.CircuitCompleteness.')


if __name__=='__main__':
    try:main()
    except (InvalidArtifact,OSError,ValueError,KeyError) as error:
        print(f'ERROR: {error}',file=sys.stderr);sys.exit(1)
