"""Lift each actual modular normalizer multiplicity column to Q(omega).

Uses the exact unnormalized source seeds and target pivot minor; the
actual group word, phase and weight projection are independently
reopened. Projector and translation stages checkpoint individually.
The normalized Weyl reference line is exact, with mod7 comparison to
the existing modular factor. No Suzuki character identification by degree.
"""
import argparse
from pathlib import Path
from time import monotonic
import json
import hashlib
import numpy as np
from scripts.x369_3b_cyclotomic_projector import CV,NORM,eig_sum,digest
from scripts.x369_3b_cyclotomic_rank import Q,ONE,ZERO,PHASE,solve_matrix
from scripts.x369_actual_3b_normalizer_tensor import WEIGHTS,source_coords
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
from scripts.x369_actual_weyl_frame_bidi import require

ROOT=Path(__file__).resolve().parent
OWNERS=('x369_3b_cyclotomic_normalizer.py','x369_3b_cyclotomic_projector.py',
        'x369_3b_cyclotomic_rank.py','x369_actual_3b_normalizer_tensor.py',
        'x369_monster_dyadic_source_action.py')


def monomial(v,coord,phase):
    a,b,t=coord;out=[ZERO]*729
    for u,c in zip(WEIGHTS,v):
        if not c:continue
        dst=tuple((x-y)%3 for x,y in zip(u,a))
        k=sum(x*3**(5-i) for i,x in enumerate(dst))
        e=(sum(x*y for x,y in zip(dst,b))+t)*phase%3
        out[k]=c*PHASE[e]
    return out


def reference(modulations,phase,weight):
    # A nonzero normalized fixed-line coordinate of the modular
    # reference implies the corresponding exact orthogonal projector
    # column is nonzero at that coordinate.
    k=WEIGHTS.index(tuple(weight));v=[ZERO]*729;v[k]=ONE
    for b in modulations:
        w=monomial(v,b,phase);t=monomial(w,b,phase)
        v=[x+y+z for x,y,z in zip(v,w,t)]
    require(bool(v[k]),'exact normalization pivot vanished')
    c=v[k].inv();v=[x*c for x in v]
    require(v[k]==ONE and all(monomial(v,b,phase)==v for b in modulations),
            'exact reference fixed line')
    return v


def run(a):
    from mmgroup import MM
    from importlib.metadata import version
    require(0<a.seconds<=90 and bool(a.resume)==bool(a.resume_sha256),'bounded source')
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256);m=local['actual_local_sources']['ternary_manifest']
    checked=check_words(m)
    left=read_pinned(a.source_rank,a.source_rank_sha256)
    right=read_pinned(a.target_rank,a.target_rank_sha256)
    mod=read_pinned(a.modular_factor,a.modular_factor_sha256);c=mod['contract']
    require(mod['status']=='actual_MMV7_normalizer_tensor_factor' and mod['full_multiplicity_rank']==90
            and c['local_sha256']==a.local_sha256 and c['source_manifest_sha256']==checked['manifest_sha256'],
            'complete actual modular normalizer factor')
    for r,z,f in ((left,c['source_zeta'],c['frame_sha256']),
                  (right,c['target_zeta'],c['target_sha256'])):
        require(r['status']=='actual_cyclotomic_rank90_minor' and
                r['local_sha256']==a.local_sha256 and r['manifest_sha256']==checked['manifest_sha256']
                and r['zeta']==z and r['frame_sha256']==f and r['normalization']==NORM and
                r['rank_exactly_90_from_source_dimension_and_Weyl'] is True,'actual cyclotomic rank scope')
    seed=read_pinned(a.seed,a.seed_sha256);j=seed['contract']['seed']
    require(0<=j<90 and left['seed_receipt_sha256'][j]==a.seed_sha256
            and seed['status']=='actual_cyclotomic_seed_lift','actual lifted seed identity')
    entry=next((x for x in m['normalizer_lifts'] if x['name']==c['lift']),None)
    require(entry is not None and MM(entry['word'])==MM(c['word']),'actual normalizer word')
    h=MM(c['word']);z=MM(m['center_word']);A=[MM(x) for x in m['translation_words']]
    B=[MM(x) for x in m['modulation_words']]
    aa=[source_coords(h**-1*g*h,z,A,B) for g in A]
    bb=[source_coords(h**-1*g*h,z,A,B) for g in B]
    # Compare canonical JSON because the earlier source returns tuples.
    canon=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'))
    require(canon(aa)==canon(mod['transformed_translation_coordinates']) and
            canon(bb)==canon(mod['transformed_modulation_coordinates']),'actual conjugation coordinates')
    phase=1 if right['zeta']==2 else 2
    weight=tuple(mod['normalization_weight'])
    phi=reference(bb,phase,weight)
    require([x.mod7() for x in phi]==mod['reference_phi'],'exact Weyl reference reduction')
    plan=[('action',h,0),('project',z,phase)]
    plan += [('project',b,phase*k) for b,k in zip(B,weight)]
    plan += [('action',g**k,0) for g,k in zip(A,weight) if k]
    contract=dict(local_sha256=a.local_sha256,source_rank_sha256=a.source_rank_sha256,
        target_rank_sha256=a.target_rank_sha256,modular_factor_sha256=a.modular_factor_sha256,
        seed_sha256=a.seed_sha256,seed=j,lift=c['lift'],source_zeta=left['zeta'],target_zeta=right['zeta'],
        normalization_weight=weight,mmgroup_version=version('mmgroup'),
        source_owners={p:digest((ROOT/p).read_bytes()) for p in OWNERS})
    contract=json.loads(canon(contract))
    cursor=0;v=CV.reopen(seed['vector'])
    if a.resume:
        r=read_pinned(a.resume,a.resume_sha256)
        require(r['contract']==contract and r['status']=='bounded_incomplete','actual resume scope')
        cursor=r['cursor'];require(0<=cursor<=len(plan),'actual source cursor')
        v=CV.reopen(r['vector'])
    while cursor<len(plan):
        if monotonic()>=deadline:break
        kind,g,k=plan[cursor]
        try:q=v.acted(g,deadline) if kind=='action' else eig_sum(v,g,k,deadline)
        except TimeoutError:break
        v=q;cursor+=1
    col=None
    if cursor==len(plan) and monotonic()<deadline:
        matrix=[[Q.wire(x) for x in row] for row in right['pivot_matrix']]
        rhs=[[Q.wire(x)/Q(NORM)] for x in v.pivots(right['pivot_indices'])]
        col=[r[0] for r in solve_matrix(matrix,rhs)]
        require([sum_q(x*y for x,y in zip(row,col)) for row in matrix]==[r[0] for r in rhs],
                'exact multiplicity pivot solve')
        require([x.mod7() for x in col]==mod['columns'][j]['coefficients'],
                'actual characteristic-zero multiplicity reduction')
    return dict(status='actual_cyclotomic_normalizer_column' if col is not None else 'bounded_incomplete',
        contract=contract,parent_receipt_sha256=a.resume_sha256,cursor=cursor,stages=len(plan),
        vector=v.wire(),reference_phi=[x.pack() for x in phi],
        coefficients=None if col is None else [x.pack() for x in col],
        modular_reduction_agrees=col is not None,
        characteristic_zero_12_plus_78_certified=False)


def sum_q(v):
    r=ZERO
    for x in v:r=r+x
    return r


def main():
    p=argparse.ArgumentParser()
    for key in ('local','source-rank','target-rank','modular-factor','seed'):
        p.add_argument('--'+key,type=Path,required=True);p.add_argument('--'+key+'-sha256',required=True)
    p.add_argument('--resume',type=Path);p.add_argument('--resume-sha256')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.output.exists():raise FileExistsError(a.output)
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,separators=(',',':'));f.write('\n')
    print(r['status'],r['cursor'],r['stages'],digest(a.output.read_bytes()))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
