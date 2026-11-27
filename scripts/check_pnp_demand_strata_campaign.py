"""Run with timeout 90s; atomic source-fingerprinted checkpoints."""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from sympy import Matrix
from check_pnp_affine_normal_components import canon,chart,lift,satisfies,Budget
from check_pnp_demand_strata import Ledger,ProbeLimit,Allowance,projector,subtract,solve_cover,rooted_probe,choose_normal,conditioned_cut_rank
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'demand-checkpoint.json'
key=hashlib.sha256(b''.join((HERE/f).read_bytes() for f in (Path(__file__).name,'check_pnp_demand_strata.py','check_pnp_affine_normal_components.py','check_pnp_normal_boundary_join.py','check_pnp_separator_row_strata.py','check_pnp_exact_cover_pair_hull.py'))).hexdigest()
state=json.loads(out.read_text()) if out.exists() else {'key':key,'cases':[]}
assert state['key']==key

def save(res):
    state['cases'].append(res);out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
def exists(name):return any(c['name']==name for c in state['cases'])
def incidence(m,S):return tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m))
for seed in range(80):
    name='small_'+str(seed)
    if exists(name):continue
    rng=Random(36927+seed);m=rng.choice((3,6,9));n=rng.randrange(3,11);R=incidence(m,[rng.sample(range(m),3) for _ in range(n)]);P=canon((r,1) for r in R)
    if P is None:continue
    u,V=chart(n,P);points=[lift(u,V,z) for z in range(1<<len(V))];L=Ledger(n,R,P);B=Budget(100_000_000);A=Matrix(m,n,lambda i,j:R[i]>>j&1);checks=empty=reuse=movement=0
    for i in range(12):
        x=rng.choice(points);H=tuple((rng.randrange(1,1<<n),rng.randrange(2)) for _ in range(i%4));caps=tuple((r&x).bit_count()-2*rng.randrange(2) for r in R);Q=canon(P+H)
        candidates=[y for y in points if satisfies(y,H,())];truth=[y for y in candidates if all((r&y).bit_count()<=a for r,a in zip(R,caps))]
        before=L.coverage(H,caps,B);assert before[0]==len(candidates)
        status,c,y=L.probe(H,caps,B,12,12,10000)
        assert status!='UNKNOWN' and c==len(truth) and (y in truth if truth else y is None)
        after=L.coverage(H,caps,B);assert after[0]==before[0] and after[1]<=before[1]
        if not truth:assert after[1]==0;empty+=1;reuse+=int(before[1]==0 and Q is not None)
        for z in points:assert projector(H,z)==int(satisfies(z,H,()))
        e=rng.randrange(m);status,c,v=rooted_probe(L,x,e,H,B,12,12,10000);assert status!='UNKNOWN'
        cap=[(r&x).bit_count() for r in R];cap[e]-=2;T=[y for y in candidates if all((r&y).bit_count()<=a for r,a in zip(R,cap))];assert c==len(T)
        if v is not None:
            y=x^v;assert y in T;q=tuple(A*Matrix([(x>>j&1)-(y>>j&1) for j in range(n)]));assert all(a>=0 and a%2==0 for a in q) and q[e]>=2;movement+=1
        checks+=1
    T=[x for x in points if all((r&x).bit_count()==1 for r in R)]
    for donor in (0,1):
        y,done=solve_cover(n,R,P,Budget(100_000_000),leaf_cap=1,seam_cap=1,nodes=2000,probe_cap=1_000_000,donor_depth=donor,cell_cap=10000)
        assert done and (y in T if T else y is None)
    save(dict(name=name,n=n,m=m,rank=len(V),checks=checks,empty=empty,reused_empty=reuse,movement=movement,charged=sum(B.stats.values()),portfolio=2))
if not exists('scope_control'):
    R=(7,7,7);P=canon(((7,1),));L=Ledger(3,R,P);B=Budget(10**6);H=canon(((7,1),(1,1),(2,1)))
    assert L.probe(H,(1,1,1),B)==('EMPTY',0,None)
    assert L.coverage((),(1,1,1),B)==(4,3)
    assert L.probe(H,(3,3,3),B)==('SAT',1,7)
    assert L.probe(H,(1,1,1),B)==('EMPTY',0,None)
    assert L.probe((),(3,-1,3),B)==('EMPTY',0,None)
    assert L.coverage((),(1,-1,1),B)==(4,0)
    assert L.coverage((),(3,3,3),B)==(4,4)
    Q=canon(((1,0),));E=canon(((2,0),));parts=subtract(Q,E,B)
    assert sum(1<<(3-len(p)) for p in parts)==2
    L2=Ledger(3,R,P);assert L2.probe((),(1,1,1),B,0,0)==('UNKNOWN',0,None) and not L2.empty
    try:L2.probe((),(1,1,1),Allowance(B,0));assert False
    except ProbeLimit:assert not L2.empty
    assert solve_cover(3,R,P,B,leaf_cap=0,seam_cap=0,nodes=1,donor_depth=0)==(None,False)
    assert conditioned_cut_rank((1,),(2,),())==0
    assert conditioned_cut_rank((1,),(2,),(3,))==1
    assert conditioned_cut_rank((1,),(1,),(1,))==0
    save(dict(name='scope_control',status='PASS',new_dependency_control='PASS'))
S=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
if not exists('original_conditioned'):
    n=30;R=incidence(18,S);P=canon((r,1) for r in R);u,V=chart(n,P);T=[lift(u,V,z) for z in range(1<<len(V))];T=[y for y in T if all((r&y).bit_count()==1 for r in R)];B=Budget(100_000_000);a=choose_normal(n,R,P,B);L=Ledger(n,R,P);masses=[]
    for b in (0,1):
        H=canon(P+((a,b),));status,c,y=L.probe(H,(1,)*18,B,8,12);assert c==sum(satisfies(z,H,()) for z in T) and status!='UNKNOWN';masses.append(c)
    assert sum(masses)==7
    y,done=solve_cover(n,R,P,Budget(100_000_000),leaf_cap=4,seam_cap=4,nodes=128,probe_cap=2_000_000,donor_depth=1)
    assert done and y in T
    save(dict(name='original_conditioned',normal=a,masses=masses,cover=y,charged=sum(B.stats.values())))
for m in (18,24,30,36):
    name='wide_'+str(m)
    if exists(name):continue
    rng=Random(369+m);S=[]
    for _ in range(5):
        while True:
            p=list(range(m));rng.shuffle(p);T=[tuple(sorted(p[i:i+3])) for i in range(0,m,3)]
            if not set(T)&set(S):break
        S.extend(T)
    rng.shuffle(S);n=len(S);R=incidence(m,S);P=canon((r,1) for r in R);B=Budget(100_000_000)
    y,done=solve_cover(n,R,P,B,leaf_cap=4,seam_cap=4,nodes=16,probe_cap=5_000_000,donor_depth=1)
    assert not done or (y is not None and all((r&y).bit_count()==1 for r in R) and satisfies(y,P,()))
    save(dict(name=name,n=n,m=m,rank=n-len(P),status='SAT' if y is not None else 'UNKNOWN',cover=y,charged=sum(B.stats.values())))
print('sources',len(state['cases']),'summary',[(k,sum(c.get(k,0) for c in state['cases'])) for k in ('checks','empty','reused_empty','movement','portfolio')]);print([c for c in state['cases'] if not c['name'].startswith('small_')])
