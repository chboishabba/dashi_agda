"""Search for *bounded* high-rank/high-width survivors of existing consumers.

No planted assignment is supplied to any producer. Refusal is UNKNOWN, not
UNSAT or an unrestricted lower bound. Atomic per-source checkpoints permit
continuation after a 90-second local timeout.
"""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import Budget,Exhausted,canon,chart,bits,satisfies
from check_pnp_normal_boundary_join import tree,value
from check_pnp_exact_cover_pair_hull import affine_disjunctive_close
from check_pnp_character_ideal import demand_character_close
from check_pnp_demand_strata import bounded_fold,solve_cover,Ledger,ProbeLimit
from check_pnp_capacity_contraction import contract
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'capacity-resistant-checkpoint.json'
# Fingerprint all direct Python donors, not just the outer script.
files=sorted(HERE.glob('check_pnp_*.py'))+[HERE/'check_p0_affine_forest_20261125.py']
key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
state=json.loads(out.read_text()) if out.exists() else dict(key=key,cases=[])
assert state['key']==key
def save(row):
    state['cases'].append(row);out.parent.mkdir(parents=True,exist_ok=True)
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
seen={c['name'] for c in state['cases']}
CAP=20_000_000
def run(fn):
    B=Budget(CAP)
    try:return fn(B),dict(B.stats),'complete'
    except (Exhausted,ProbeLimit,RecursionError):return None,dict(B.stats),'refused'
for m in (18,24,30,36,42):
    for degree in (5,7,9):
        for seed in range(4):
            name=f'{m}_{degree}_{seed}'
            if name in seen:continue
            rng=Random(3692700+100*m+10*degree+seed);S=[]
            for _ in range(degree):
                for attempt in range(1000):
                    p=list(range(m));rng.shuffle(p)
                    T=[tuple(sorted(p[i:i+3])) for i in range(0,m,3)]
                    if not set(T)&set(S):break
                else:raise AssertionError('fixture generation cap')
                S.extend(T)
            rng.shuffle(S);n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m))
            P=canon((r,1) for r in R);assert P is not None
            u,V=chart(n,P);d=len(V);F=tuple(tuple((1<<j,0) for j in bits(r)) for r in R)
            G=tuple(tuple((value(V,a),(a&u).bit_count()%2) for a,b in row) for row in F)
            def measure(B):
                root,boundary,space=tree(d,G,B);todo=[root];w=0
                while todo:
                    mask,A,C=todo.pop();w=max(w,len(boundary(mask)))
                    if A is not None:todo.extend((A,C))
                return w
            width,ws,wstatus=run(measure);A=Matrix(m,n,lambda i,j:R[i]>>j&1)
            def check(y):
                assert satisfies(y,P,()) and all(x==1 for x in A*Matrix([y>>j&1 for j in range(n)]))
            observations={};found=None
            for lane,fn in (
                ('disjunctive',lambda B:affine_disjunctive_close(n,F,B,P,depth=1,rounds=1)),
                ('character',lambda B:demand_character_close(n,F,P,B,degree=1,max_pivots=256,section_cap=8,path_steps=8,adaptive_nodes=8,adaptive_provenance=True)),
                ('separator',lambda B:bounded_fold(n,R,P,(1,)*m,B,8,8))):
                z,stats,status=run(fn)
                entry=dict(status=status,charged=sum(stats.values()))
                if z is not None:
                    Q,y=z
                    if lane!='separator':
                        assert Q is not None # known planted, never supplied
                        entry['rank_gain']=len(Q)-len(P)
                    else:assert Q>0
                    if y is not None:check(y);entry['witness']=y;found=y
                observations[lane]=entry
            # Run new producers on a genuine baseline refusal, not only easy cases.
            survived=found is None
            if survived:
                for lane,fn in (
                    ('collective',lambda B:contract(n,R,P,(1,)*m,B)),
                    ('demand_portfolio',lambda B:solve_cover(n,R,P,B,leaf_cap=8,seam_cap=8,nodes=12,probe_cap=1_000_000,donor_depth=1,character_degree=1))):
                    z,stats,status=run(fn)
                    entry=dict(status=status,charged=sum(stats.values()))
                    if lane=='demand_portfolio' and z is not None:
                        y,done=z;assert not done or y is not None
                    else:y=z
                    if y is not None:check(y);entry['witness']=y;found=y
                    observations[lane]=entry
            high=width is not None and d>=16 and width>=12
            save(dict(name=name,n=n,m=m,rank=d,width=width,width_status=wstatus,
                width_charged=sum(ws.values()),observations=observations,
                bounded_baseline_survivor=bool(high and survived),
                bounded_combined_survivor=bool(high and survived and found is None),
                outcome='SAT' if found is not None else 'UNKNOWN'))
print('sources',len(state['cases']),'baseline_survivors',sum(c['bounded_baseline_survivor'] for c in state['cases']),
      'combined_survivors',sum(c['bounded_combined_survivor'] for c in state['cases']))
