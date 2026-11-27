"""User-run acceptance: original capacity floors, signed bounds and reopening.
Run under timeout 90s; no CI. Atomic fingerprinted per-source receipts.
"""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import Budget,canon,chart,lift,satisfies
from check_pnp_demand_strata import Ledger,Allowance,ProbeLimit,solve_cover
from check_pnp_capacity_geometry import violation_flats
from check_pnp_capacity_signed import observe,observe_ledger,relative,select
from check_pnp_capacity_contraction import admissible_floor,contract
from check_pnp_adaptive_signed_escape import certificate,reopen,point
from check_pnp_partial_quotient import block_witness
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'capacity-sufficient-checkpoint.json'
files=sorted(HERE.glob('check_pnp_*.py'))+[HERE/'check_p0_signed_conflict_20261126.py']
key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
state=json.loads(out.read_text()) if out.exists() else dict(key=key,cases=[])
assert state['key']==key
def save(row):
    state['cases'].append(row);out.parent.mkdir(parents=True,exist_ok=True)
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
seen={c['name'] for c in state['cases']}
if 'guarded' not in seen:
    F=tuple(canon(G) for G in (((1,0),),((1,0),(2,0)),((1,0),(2,1))))
    B=Budget(100000);q=certificate(2,F,(2,),B,admissible_envelope=admissible_floor)
    assert q is not None and satisfies(reopen(q[1],1,B),(),F)
    F=tuple(canon(G) for G in (((1,0),(2,0)),((1,0),(2,1))))
    q=block_witness(2,F,(2,),B,promotions=0)
    assert q is not None and satisfies(q[0],(),F)
    save(dict(name='guarded',charged=sum(B.stats.values())))
for seed in range(80):
    name=f'small_{seed}'
    if name in seen:continue
    rng=Random(3692700+seed);n=rng.randrange(3,9);R=tuple(rng.randrange(1,1<<n) for _ in range(3))
    H=canon((r,1) for r in R)
    if H is None:continue
    # No column is outside all original rows for exact separator comparison.
    if (R[0]|R[1]|R[2])!=(1<<n)-1:continue
    u,V=chart(n,H);X=[lift(u,V,z) for z in range(1<<len(V))]
    A=Matrix(3,n,lambda i,j:R[i]>>j&1)
    B=Budget(100_000_000);checks=0;witnesses=0;exact=0;relative_choices=0
    for t in range(8):
        caps=tuple(rng.randrange(0,r.bit_count()+1) for r in R)
        p=canon(H+((1<<rng.randrange(n),rng.randrange(2)),))
        if p is None:continue
        Y=[x for x in X if satisfies(x,p,())]
        T=[x for x in Y if all(v<=c for v,c in zip(A*Matrix([x>>j&1 for j in range(n)]),caps))]
        F=violation_flats(n,R,p,caps,B)
        assert all(satisfies(x,(),F)==(x in T) for x in Y)
        a=1<<rng.randrange(n)
        I=observe(n,R,p,caps,Allowance(B,2_000_000),a,promotions=12)
        counts=[sum(int(bool(x&a))==b for x in T) for b in (0,1)]
        for b,v in enumerate(I):
            assert v.lower<=counts[b]<=v.upper
            if v.witness is not None:
                assert v.witness in T and int(bool(v.witness&a))==b;witnesses+=1
            exact+=v.lower==v.upper
        D=relative(I)
        if T:
            from fractions import Fraction
            assert D is not None and D[0]<=Fraction(counts[0]-counts[1],len(T))<=D[1]
        b=select(I)
        if b is not None:assert counts[b]>0;relative_choices+=1
        # Scope transport: reuse an exact original empty child, if available.
        L=Ledger(n,R,H)
        for b,count in enumerate(counts):
            Q=canon(p+((a,b),))
            if Q is not None and count==0:
                status,_,_=L.probe(Q,caps,B,8,8)
                assert status=='EMPTY'
        J=observe_ledger(L,p,caps,a,Allowance(B,2_000_000))
        assert all(v.lower<=counts[b]<=v.upper for b,v in enumerate(J))
        K=observe(n,R,p,caps,Allowance(B,0),a)
        assert all(v.lower<=counts[b]<=v.upper for b,v in enumerate(K))
        try:
            y=contract(n,R,p,caps,Allowance(B,500_000))
            if y is not None:assert y in T;witnesses+=1
        except ProbeLimit:pass
        checks+=1
    save(dict(name=name,checks=checks,witnesses=witnesses,exact=exact,relative_choices=relative_choices,charged=sum(B.stats.values())))
if 'original_30' not in seen:
    S=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
    n=30;R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(18))
    H=canon((r,1) for r in R);u,V=chart(n,H);A=Matrix(18,n,lambda i,j:R[i]>>j&1)
    T=[x for z in range(1<<len(V)) if all((r&(x:=lift(u,V,z))).bit_count()==1 for r in R)]
    assert len(T)==7
    B=Budget(100_000_000);a=8
    I=observe(n,R,H,(1,)*18,Allowance(B,10_000_000),a)
    J=observe_ledger(Ledger(n,R,H),H,(1,)*18,a,Allowance(B,20_000_000),leaf_cap=12,seam_cap=12)
    counts=[sum(int(bool(x&a))==b for x in T) for b in (0,1)]
    for obs in (I,J):
        assert all(v.lower<=counts[b]<=v.upper for b,v in enumerate(obs))
        for v in obs:
            if v.witness is not None:assert all(x==1 for x in A*Matrix([v.witness>>j&1 for j in range(n)]))
    y,done=solve_cover(n,R,H,B,nodes=32,probe_cap=2_000_000,character_degree=1)
    if y is not None:assert y in T
    assert not done or y is not None
    save(dict(name='original_30',truth=counts,signed=[v.__dict__ for v in I],combined=[v.__dict__ for v in J],witness=y,decisive=done,charged=sum(B.stats.values())))
print('cases',len(state['cases']),{k:sum(c.get(k,0) for c in state['cases']) for k in ('checks','witnesses','exact','relative_choices')})
