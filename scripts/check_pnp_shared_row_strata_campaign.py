from pathlib import Path
from random import Random
from collections import Counter
import json,os,sys,hashlib
from sympy import Matrix
from check_pnp_affine_normal_components import *
from check_pnp_shared_row_strata import build,observe,descent
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'checkpoint.json'
key=hashlib.sha256(Path(__file__).read_bytes()+(HERE/'check_pnp_shared_row_strata.py').read_bytes()+(HERE/'check_pnp_affine_normal_components.py').read_bytes()).hexdigest()
state=json.loads(out.read_text()) if out.exists() else {'key':key,'cases':[]}
assert state.get('key')==key, 'stale checkpoint: use a new path'
out.parent.mkdir(parents=True,exist_ok=True)
def save():
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
def run(name,S,m,x=None):
    if any(z['name']==name for z in state['cases']):return
    n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m));P=canon((r,1) for r in R)
    if P is None:return
    u,V=chart(n,P);d=len(V)
    if d>16:return
    rng=Random(name);x=lift(u,V,rng.randrange(1<<d)) if x is None else x
    B=Budget(100_000_000);C=build(n,R,P,B);buildcost=sum(B.stats.values());assert C is not None
    points=[lift(u,V,z) for z in range(1<<d)]
    xs=[x]+[points[rng.randrange(len(points))] for _ in range(3)]
    A=Matrix(m,n,lambda i,j:(R[i]>>j)&1);rows=[]
    for x in xs:
        w=tuple((r&x).bit_count() for r in R)
        T=[y for y in points if all((r&y).bit_count()<=k for r,k in zip(R,w))]
        good=[y for y in T if y!=x and any((r&y).bit_count()<k for r,k in zip(R,w))]
        roots=tuple(sum((r&y).bit_count()<k for y in T) for r,k in zip(R,w));covers=sum(all((r&y).bit_count()==1 for r in R) for y in points)
        before=sum(B.stats.values());status,v,rc,cc=observe(n,R,P,x,C,B);cost=sum(B.stats.values())-before
        assert roots==rc and covers==cc and (status=='SAT')==bool(good)
        if v is not None:
            y=x^v;assert y in good
            q=tuple(A*Matrix([(x>>j&1)-(y>>j&1) for j in range(n)]));assert all(a>=0 and a%2==0 for a in q) and any(q)
        rows.append(dict(x=x,status=status,y=None if v is None else x^v,root_counts=rc,cover_count=cc,trade_count=len(good),observe_cost=cost))
    H=[];result=descent(n,R,P,x,Budget(100_000_000),history=H,k_index=7)
    assert result is not None and result[1] and (result[0] is not None)==bool(covers)
    if result[0] is not None:assert result[0] in points and all((r&result[0]).bit_count()==1 for r in R)
    if H:assert H[0][:2]==(7,0)
    state['cases'].append(dict(name=name,rank=d,n=n,m=m,build_cost=buildcost,observations=rows));save()
S=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
run('original_regression',S,18,181773997)
# Independent regular planted sources: 5 disjoint partitions, distinct triples.
for seed in range(9):
    rng=Random(36900+seed);S=[]
    for _ in range(5):
        while True:
            p=list(range(18));rng.shuffle(p);T=[tuple(sorted(p[i:i+3])) for i in range(0,18,3)]
            if not set(T)&set(S):break
        S.extend(T)
    run('new_regular_'+str(seed),S,18)
for seed in range(90):
    rng=Random(12300+seed);m=rng.choice((3,6,9,12));n=rng.randrange(1,12);S=[tuple(rng.sample(range(m),3)) for _ in range(n)];run('small_'+str(seed),S,m)
# Rank and budget refusal controls.
P=canon(((7,1),));assert build(3,(7,),P,Budget(10000),rank_cap=1) is None
try:build(3,(7,),P,Budget(0));assert False
except Exhausted:pass
state['refusal_controls']='PASS';save()
print('cases',len(state['cases']),'observations',sum(len(x['observations']) for x in state['cases']))
print('first',state['cases'][0]);print('status',Counter(y['status'] for x in state['cases'] for y in x['observations']))
