"""Replay bounded survivors at the original 20m lane cap, independently verified."""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import Budget,canon,bits,satisfies
from check_pnp_demand_strata import Allowance,ProbeLimit,bounded_fold
from check_pnp_capacity_partition import partition
from check_pnp_exact_cover_pair_hull import affine_disjunctive_close
from check_pnp_character_ideal import demand_character_close
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'capacity-partition-replay.json'
files=sorted(HERE.glob('check_pnp_*.py'))+[HERE/'check_p0_affine_forest_20261125.py',HERE/'check_p0_signed_conflict_20261126.py']
key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
state=json.loads(out.read_text()) if out.exists() else dict(key=key,cases=[])
assert state['key']==key
seen={c['name'] for c in state['cases']}
def save(row):
    state['cases'].append(row);out.parent.mkdir(parents=True,exist_ok=True)
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
def run(fn,cap):
    B=Budget(cap)
    try:return fn(Allowance(B,cap)),dict(B.stats)
    except ProbeLimit:return None,dict(B.stats)
for name,m,degree,seed in [('24_9_2',24,9,2),('sparse_36_1',36,0,1),('sparse_36_2',36,0,2),('sparse_42_0',42,0,0),('sparse_42_2',42,0,2)]:
    if degree:
        rng=Random(3692700+100*m+10*degree+seed);S=[]
        for _ in range(degree):
            for attempt in range(1000):
                p=list(range(m));rng.shuffle(p)
                T=[tuple(sorted(p[i:i+3])) for i in range(0,m,3)]
                if not set(T)&set(S):break
            else:raise AssertionError('fixture generation cap')
            S.extend(T)
    else:
        rng=Random(3692710+m*10+seed);p=list(range(m));rng.shuffle(p)
        S={tuple(sorted(p[i:i+3])) for i in range(0,m,3)}
        while len(S)<(5*m)//3:S.add(tuple(sorted(rng.sample(range(m),3))))
        S=sorted(S)
    rng.shuffle(S);n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m))
    P=canon(tuple((r,1) for r in R));A=Matrix(m,n,lambda i,j:R[i]>>j&1)
    F=tuple(tuple((1<<j,0) for j in bits(r)) for r in R)
    def verify(y):assert satisfies(y,P,()) and all(x==1 for x in A*Matrix([y>>j&1 for j in range(n)]))
    lanes=[('partition',lambda B:partition(n,R,P,(1,)*m,B,nodes=256))]
    if not degree:lanes += [('disjunctive',lambda B:affine_disjunctive_close(n,F,B,P,depth=1,rounds=1)),('character',lambda B:demand_character_close(n,F,P,B,degree=1,max_pivots=256,section_cap=8,path_steps=8,adaptive_nodes=8,adaptive_provenance=True))]
    for lane,fn in lanes:
        k=name+'/'+lane
        if k in seen:continue
        z,stats=run(fn,20_000_000)
        if lane=='partition':
            assert z is not None and z.upper>0;y=z.witness;detail=z.__dict__
        else:
            if z is not None:assert z[0] is not None
            y=None if z is None else z[1];detail=None if z is None else len(z[0])-len(P)
        if y is not None:verify(y)
        save(dict(name=k,n=n,m=m,rank=n-len(P),witness=y,detail=detail,charged=sum(stats.values()),charges=stats))
        print(k,y is not None,sum(stats.values()),flush=True)
