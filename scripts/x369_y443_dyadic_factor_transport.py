"""Exact original Y443 factor-action transport on actual dyadic V2.

Consumes the actual quotient receipt and reuses the accepted primitive
source reconstruction and Griess axis basis constructor. Independently
evaluate the right factor, and conjugate the left factor by the actual
central-swap coordinate. These are two realizations of the SAME source
word, not independent original FLM/JMD VOA streams.
"""
import argparse
import hashlib
import json
from pathlib import Path
from time import monotonic
from scripts.x369_y443_actual_monster_quotient import NODES, U, V, relators, evaluate, recover_pair, require
from scripts.x369_monster_dyadic_source_action import action, verify, unit, DIM
from scripts.x369_actual_griess_axis_generation import basis_terms, exact_sum

ROOT=Path(__file__).resolve().parent
OWNERS=('x369_y443_actual_monster_quotient.py','x369_y443_dyadic_factor_transport.py',
        'x369_monster_dyadic_source_action.py','x369_actual_griess_axis_generation.py')
SPECIMENS=(0,23,24,299,300,575,576,851,852,49427,49428,98579,98580,147731,147732,196883)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def load(path,digest):
    raw=path.read_bytes()
    require(sha(raw)==digest,'pinned source receipt identity')
    return json.loads(raw)


def reopen_source(r):
    from mmgroup import MM
    require(r['status']=='actual_Y443_Monster_quotient_source' and
            r['original_relator_checks']==list(range(80)),'full original relation receipt')
    require(set(r['original_node_words'])==set(r['second_factor_node_words'])==set(NODES),'node scope')
    left={n:MM(r['original_node_words'][n]) for n in NODES}
    right={n:MM(r['second_factor_node_words'][n]) for n in NODES}
    a=MM(r['central_swap_first_word']);one=MM(1)
    require(all(left[n]!=one and right[n]==a**-1*left[n]*a for n in NODES),
            'source factor conjugation changed')
    u,v,w,words=recover_pair(left,one)
    require(words==r['node_words_in_jmd_pair'] and u==MM(r['words']['u']) and v==MM(r['words']['v']),
            'actual JMD word identities changed')
    ur,vr,_,_=recover_pair(right,one)
    require(ur==MM(r['second_factor_pair']['u']) and vr==MM(r['second_factor_pair']['v']),
            'second factor pair changed')
    return {'u':u,'v':v},{'u':ur,'v':vr},a


def run(a):
    from importlib.metadata import version
    require(0<a.seconds<=90 and bool(a.resume)==bool(a.resume_sha256),'bounded scope')
    source=load(a.source,a.source_sha256)
    left,right,t=reopen_source(source)
    deadline=monotonic()+a.seconds
    # Fixed cross-tag audit; optionally all source columns in declared range.
    inds=SPECIMENS if a.start is None else tuple(range(a.start,a.start+a.count))
    scope=[(g,i) for g in ('u','v') for i in inds]
    contract=dict(source_sha256=a.source_sha256,mmgroup_version=version('mmgroup'),
        start=a.start,count=a.count,owners={n:sha((ROOT/n).read_bytes()) for n in OWNERS})
    rows=[]
    if a.resume:
        old=load(a.resume,a.resume_sha256)
        require(old['contract']==contract and old['status']=='bounded_incomplete','source scope changed')
        rows=old['rows']
        require([(r['generator'],r['column']) for r in rows]==scope[:len(rows)],
                'missing or repeated audit columns')
    for g,i in scope[len(rows):]:
        if monotonic()>=deadline:break
        try:
            x=unit(i)
            # Actual source basis expression, independent of group transport.
            require(exact_sum(basis_terms(i),deadline).same(x),'axis source basis mismatch')
            y=action(x,right[g],deadline)
            # Right action convention: x*a^-1*left*g? Precisely
            # right[g] = a^-1 left[g] a, hence apply in this order.
            z=action(action(action(x,t**-1,deadline),left[g],deadline),t,deadline)
            require(z.same(y),'actual characteristic-zero factor square')
            verify(x,y,right[g])
        except TimeoutError:break
        rows.append(dict(generator=g,column=i,output_sha256=y.digest(),
                         nonzero=len(y.sparse()),denominator_power=y.power,
                         exact_axis_basis_reopened=True,exact_factor_square=True))
    complete=len(rows)==len(scope)
    return dict(status='actual_Y443_dyadic_factor_transport' if complete else 'bounded_incomplete',
        contract=contract,parent_receipt_sha256=a.resume_sha256,columns_required=len(scope),
        columns_verified=len(rows),rows=rows,
        full_u_v_columns_verified=complete and len(scope)==2*DIM,
        same_group_word_factor_conjugation_certified=True,
        independent_original_selected_FLM_VOA_agreement=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--source',type=Path,required=True);p.add_argument('--source-sha256',required=True)
    p.add_argument('--start',type=int);p.add_argument('--count',type=int)
    p.add_argument('--resume',type=Path);p.add_argument('--resume-sha256')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    require((a.start is None and a.count is None) or
            (a.start is not None and a.count is not None and 0<=a.start<DIM and 0<a.count<=DIM-a.start),
            'declared source range')
    if a.output.exists():raise FileExistsError(a.output)
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(r['status'],r['columns_verified'],r['columns_required'],sha(a.output.read_bytes()))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
