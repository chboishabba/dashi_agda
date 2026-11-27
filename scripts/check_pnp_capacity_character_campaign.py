"""Bounded capacity weld acceptance; atomic per-case checkpoints."""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import canon,chart,lift,satisfies,Budget
from check_pnp_demand_strata import Ledger,Allowance,ProbeLimit
from check_pnp_capacity_character import (capacity_chart,extend_original,discover_certificate,
    verify_certificate,Certificate,mass_interval,reopen_positive,signed_interval,preferred_child)
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'capacity-checkpoint.json'
files=(Path(__file__).name,'check_pnp_capacity_character.py','check_pnp_demand_strata.py',
       'check_pnp_character_ideal.py','check_pnp_affine_normal_components.py',
       'check_p0_affine_forest_20261125.py','check_pnp_normal_boundary_join.py',
       'check_pnp_separator_row_strata.py')
key=hashlib.sha256(b''.join((HERE/f).read_bytes() for f in files)).hexdigest()
state=json.loads(out.read_text()) if out.exists() else dict(key=key,cases=[])
assert state['key']==key
def save(row):
    state['cases'].append(row);out.parent.mkdir(parents=True,exist_ok=True)
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
def done(name):return any(c['name']==name for c in state['cases'])
for seed in range(36):
    name='small_'+str(seed)
    if done(name):continue
    rng=Random(369+seed);n=rng.randrange(3,9);m=3
    R=tuple(rng.randrange(1,1<<n) for _ in range(m));P=canon((r,1) for r in R)
    if P is None:continue
    A=Matrix(m,n,lambda i,j:R[i]>>j&1);u,V=chart(n,P)
    X=[lift(u,V,z) for z in range(1<<len(V))];B=Budget(300_000_000)
    counts=dict(extensions=0,intervals=0,proofs=0,witnesses=0,refusals=0)
    for t in range(6):
        caps=tuple(rng.randrange(1,1+r.bit_count()) for r in R)
        H=canon(P+((1<<rng.randrange(n),rng.randrange(2)),))
        if H is None:continue
        points=[x for x in X if satisfies(x,H,())]
        truth=[x for x in points if all(a<=c for a,c in zip(A*Matrix([x>>j&1 for j in range(n)]),caps))]
        C=capacity_chart(n,R,H,caps,B)
        for x in points:
            y=extend_original(x,C)
            assert (y is not None)==(x in truth)
            if y is not None:assert y&((1<<n)-1)==x
            counts['extensions']+=1
        I=mass_interval(n,R,H,caps,B)
        assert I[0]<=len(truth)<=I[1];counts['intervals']+=1
        w=reopen_positive(n,R,H,caps,I,B)
        if w is not None:assert w in truth;counts['witnesses']+=1
        a=1<<rng.randrange(n);Q,J,D=signed_interval(n,R,H,caps,a,B)
        d=sum(1 if not x&a else -1 for x in truth);assert D[0]<=d<=D[1]
        b=preferred_child(J,D,bool(truth))
        if b is not None:assert any(int(bool(x&a))==b for x in truth)
        try:
            cert=discover_certificate(n,R,H,caps,Allowance(B,200_000),degree=0)
            if cert is not None:
                assert verify_certificate(n,R,H,caps,cert,B) and not truth
                counts['proofs']+=1
        except ProbeLimit:counts['refusals']+=1
    save(dict(name=name,**counts,charged=sum(B.stats.values())))
if not done('scope'):
    n=4;R=(7,7,7);P=canon(((7,1),));H=canon(P+((1,1),(2,1)))
    B=Budget(100_000_000);caps=(1,1,1)
    children=[discover_certificate(n,R,canon(H+((8,b),)),caps,B,0) for b in (0,1)]
    assert all(children)
    cert=Certificate('siblings',normal=8,children=tuple(children))
    assert verify_certificate(n,R,H,caps,cert,B)
    assert not verify_certificate(n,R,H,(3,3,3),cert,B)
    L=Ledger(n,R,P)
    status,c,y=L.probe(H,caps,B,0,0,character_degree=0)
    assert (status,c,y)==('EMPTY',0,None)
    assert L.probe(H,(3,3,3),B,8,8)[0]=='SAT'
    save(dict(name='scope',status='PASS',charged=sum(B.stats.values())))
print('capacity weld',len(state['cases']),{k:sum(c.get(k,0) for c in state['cases']) for k in ('extensions','intervals','proofs','witnesses','refusals')})
