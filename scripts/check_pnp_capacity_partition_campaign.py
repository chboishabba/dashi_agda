"""Local checkpointed tests of disjoint original row-fibre continuation.

Sparse planted instances use one hidden partition plus random distractors,
not a union of several full partitions. Reference enumeration is separate
from all producers. A bounded refusal is never a complexity lower bound.
"""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import Budget,canon,chart,lift,satisfies,bits
from check_pnp_demand_strata import Allowance,ProbeLimit,bounded_fold
from check_pnp_capacity_partition import row_cells,partition
from check_pnp_exact_cover_pair_hull import affine_disjunctive_close
from check_pnp_character_ideal import demand_character_close
from check_pnp_normal_boundary_join import tree,value
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'capacity-partition-checkpoint.json'
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
for seed in range(120):
    name=f'small_{seed}'
    if name in seen:continue
    rng=Random(3692701+seed);n=rng.randrange(1,10);R=tuple(rng.randrange(1,1<<n) for _ in range(rng.randrange(1,6)))
    H=canon(tuple((r,1) for r in R));checks=0;positive=0;empty=0;unknown=0
    if H is None:continue
    u,V=chart(n,H);X=[lift(u,V,z) for z in range(1<<len(V))];A=Matrix(len(R),n,lambda i,j:R[i]>>j&1)
    B=Budget(50_000_000)
    for _ in range(5):
        P=canon(H+((1<<rng.randrange(n),rng.randrange(2)),));caps=tuple(rng.randrange(r.bit_count()+1) for r in R)
        if P is None:continue
        Y=[x for x in X if satisfies(x,P,())]
        T=[x for x in Y if all(v<=c for v,c in zip(A*Matrix([x>>j&1 for j in range(n)]),caps))]
        for r,c in zip(R,caps):
            C=row_cells(n,P,r,c,Allowance(B,1_000_000))
            assert C is not None
            assert all(sum(satisfies(x,Q,()) for Q in C)==int((r&x).bit_count()<=c) for x in Y)
        for limit in (0,1,3,32):
            v=partition(n,R,P,caps,Allowance(B,1_000_000),nodes=limit)
            assert 0<=v.lower<=len(T)<=v.upper
            if v.witness is not None:assert v.witness in T;positive+=1
            elif v.upper==0:assert not T;empty+=1
            else:unknown+=1
            checks+=1
        v=partition(n,R,P,caps,Allowance(B,0));assert v.lower<=len(T)<=v.upper
    save(dict(name=name,checks=checks,positive=positive,empty=empty,unknown=unknown,charged=sum(B.stats.values())))
# The baseline cap is explicit: comparisons are against a bounded portfolio.
for m in (24,30,36,42):
    for seed in range(4):
        name=f'sparse_{m}_{seed}'
        if name in seen:continue
        rng=Random(3692710+m*10+seed);p=list(range(m));rng.shuffle(p)
        S={tuple(sorted(p[i:i+3])) for i in range(0,m,3)}
        planted=set(S)
        while len(S)<(5*m)//3:
            S.add(tuple(sorted(rng.sample(range(m),3))))
        S=sorted(S);rng.shuffle(S);n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m))
        P=canon(tuple((r,1) for r in R));u,V=chart(n,P);d=len(V)
        hidden=sum(1<<j for j,T in enumerate(S) if T in planted);assert all((r&hidden).bit_count()==1 for r in R)
        A=Matrix(m,n,lambda i,j:R[i]>>j&1)
        F=tuple(tuple((1<<j,0) for j in bits(r)) for r in R)
        def verify(y):assert satisfies(y,P,()) and all(x==1 for x in A*Matrix([y>>j&1 for j in range(n)]))
        def width(B):
            G=tuple(tuple((value(V,a),(a&u).bit_count()%2) for a,b in row) for row in F)
            root,boundary,_=tree(d,G,B);todo=[root];w=0
            while todo:
                mask,L,C=todo.pop();w=max(w,len(boundary(mask)))
                if L is not None:todo.extend((L,C))
            return w
        w,_=run(width,2_000_000);obs={};found=False
        for lane,fn in (
            ('disjunctive',lambda B:affine_disjunctive_close(n,F,B,P,depth=1,rounds=1)),
            ('character',lambda B:demand_character_close(n,F,P,B,degree=1,max_pivots=256,section_cap=8,path_steps=8,adaptive_nodes=8,adaptive_provenance=True)),
            ('separator',lambda B:bounded_fold(n,R,P,(1,)*m,B,8,8))):
            z,stats=run(fn,1_000_000);y=None if z is None else z[1]
            if z is not None:assert z[0] is not None and (lane!='separator' or z[0]>0)
            if y is not None:verify(y);found=True
            obs[lane]=dict(witness=y,charged=sum(stats.values()),charges=stats)
        v,stats=run(lambda B:partition(n,R,P,(1,)*m,B,nodes=64),1_000_000)
        assert v is not None and v.upper>0
        if v.witness is not None:verify(v.witness)
        obs['partition']=dict(bound=v.__dict__,charged=sum(stats.values()),charges=stats)
        save(dict(name=name,n=n,m=m,rank=d,width=w,baseline_survivor=not found,partition_resolved=v.witness is not None,observations=obs))
print('cases',len(state['cases']),{k:sum(c.get(k,0) for c in state['cases']) for k in ('checks','positive','empty','unknown','baseline_survivor','partition_resolved')})
