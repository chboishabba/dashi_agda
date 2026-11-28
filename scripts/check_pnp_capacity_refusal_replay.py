"""Replay every bounded refusal from the original partition small campaign.
No reference assignment is passed to producers. One shared logical clock
per observation, same node cutoff; a different existing consumer may run.
"""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import Budget,canon,chart,lift,satisfies
from check_pnp_demand_strata import Allowance
from check_pnp_capacity_partition import partition
HERE=Path(__file__).parent
out=Path(sys.argv[1])
files=sorted(HERE.glob('check_pnp_*.py'))+[HERE/'check_p0_affine_forest_20261125.py',HERE/'check_p0_signed_conflict_20261126.py']
key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
state=json.loads(out.read_text()) if out.exists() else dict(key=key,cases=[])
assert state['key']==key
seen={c['name'] for c in state['cases']}
def save(row):
    state['cases'].append(row);out.parent.mkdir(parents=True,exist_ok=True)
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
for seed in range(120):
    name=f'small_{seed}'
    if name in seen:continue
    rng=Random(3692701+seed);n=rng.randrange(1,10);R=tuple(rng.randrange(1,1<<n) for _ in range(rng.randrange(1,6)))
    H=canon(tuple((r,1) for r in R))
    if H is None:continue
    u,V=chart(n,H);X=[lift(u,V,z) for z in range(1<<len(V))];A=Matrix(len(R),n,lambda i,j:R[i]>>j&1)
    records=[]
    for i in range(5):
        P=canon(H+((1<<rng.randrange(n),rng.randrange(2)),));caps=tuple(rng.randrange(r.bit_count()+1) for r in R)
        if P is None:continue
        Y=[x for x in X if satisfies(x,P,())]
        T=[x for x in Y if all(v<=c for v,c in zip(A*Matrix([x>>j&1 for j in range(n)]),caps))]
        for limit in (0,1,3,32):
            B=Budget(1_000_000);v=partition(n,R,P,caps,Allowance(B,B.left),nodes=limit)
            if v.witness is not None or v.upper==0:continue
            assert v.lower<=len(T)<=v.upper
            C=Budget(1_000_000);w=partition(n,R,P,caps,Allowance(C,C.left),nodes=limit,recovery=True)
            assert w.lower<=len(T)<=w.upper
            if w.witness is not None:assert w.witness in T
            if w.upper==0:assert not T
            z=partition(n,R,P,caps,Allowance(Budget(0),0),nodes=limit,recovery=True)
            assert z.lower<=len(T)<=z.upper
            records.append(dict(trial=i,normal_demand=P,caps=caps,limit=limit,truth_count=len(T),baseline=v.__dict__,combined=w.__dict__,baseline_charged=sum(B.stats.values()),charges=dict(C.stats),outcome='SAT' if w.witness is not None else 'EMPTY' if w.upper==0 else 'UNKNOWN'))
    save(dict(name=name,n=n,rows=R,cases=records))
rows=[r for c in state['cases'] for r in c['cases']]
from collections import Counter
print('refusals',len(rows),'by_node_limit',dict(Counter(r['limit'] for r in rows)),'truth_inhabited',sum(r['truth_count']>0 for r in rows),'outcomes',dict(Counter(r['outcome'] for r in rows)))
assert len(rows)==243
