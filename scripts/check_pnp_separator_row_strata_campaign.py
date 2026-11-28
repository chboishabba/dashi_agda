"""Checkpointed exact acceptance; timeout 90s python this_script.py receipt.json."""
import hashlib,json,os,sys
from pathlib import Path
from random import Random
from collections import Counter
from sympy import Matrix
from check_pnp_affine_normal_components import canon,chart,lift,Budget,Exhausted
from check_pnp_separator_row_strata import build,observe
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'seam-checkpoint.json'
key=hashlib.sha256(b''.join((HERE/f).read_bytes() for f in (Path(__file__).name,'check_pnp_separator_row_strata.py','check_pnp_affine_normal_components.py','check_pnp_normal_boundary_join.py'))).hexdigest()
state=json.loads(out.read_text()) if out.exists() else {'key':key,'cases':[]}
assert state['key']==key

def save():
    out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)

def run(name,S,m,x=None,pins=(),expected=None,cap=8):
    if any(c['name']==name for c in state['cases']):return
    n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m));P=canon(tuple((r,1) for r in R)+tuple(pins))
    if P is None:return
    u,V=chart(n,P);d=len(V);rng=Random(name);x=lift(u,V,rng.randrange(1<<d)) if x is None else x
    B=Budget(10**8);G=build(n,R,P,B,cap,cap);bc=sum(B.stats.values());res=dict(name=name,n=n,m=m,rank=d,build_cost=bc)
    if G is None:
        assert expected is None;res['status']='WIDTH_REFUSAL';state['cases'].append(res);save();return
    res['width']=G[-1];res['observations']=[]
    points=[lift(u,V,z) for z in range(1<<d)] if d<=14 else None
    A=Matrix(m,n,lambda i,j:R[i]>>j&1)
    for incumbent in [x]+([points[rng.randrange(len(points))] for _ in range(2)] if points is not None else []):
        before=sum(B.stats.values());status,v,roots,covers,mass=observe(n,R,P,incumbent,G,B);cost=sum(B.stats.values())-before
        w=tuple((r&incumbent).bit_count() for r in R)
        if points is not None:
            T=[y for y in points if all((r&y).bit_count()<=a for r,a in zip(R,w))]
            assert len(T)==mass and covers==sum(all((r&y).bit_count()==1 for r in R) for y in points)
            assert roots==tuple(sum((r&y).bit_count()<a for y in T) for r,a in zip(R,w))
            assert (status=='SAT')==any(roots)
        if expected is not None:assert (covers,mass,roots)==expected
        y=None if v is None else incumbent^v
        if y is not None:
            q=tuple(A*Matrix([(incumbent>>j&1)-(y>>j&1) for j in range(n)]));assert all(a>=0 and a%2==0 for a in q) and any(q)
            if covers:assert all((r&y).bit_count()==1 for r in R)
        res['observations'].append(dict(x=incumbent,y=y,status=status,cover_count=covers,admissible_mass=mass,root_counts=roots,observe_cost=cost))
    state['cases'].append(res);save();print(name,d,res['width'],flush=True)

S=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
run('original_regression',S,18,181773997,cap=12)
for seed in range(70):
    rng=Random(36900+seed);m=rng.choice((3,6,9,12));n=rng.randrange(1,13);S=[tuple(rng.sample(range(m),3)) for _ in range(n)];run('small_'+str(seed),S,m)
for b in (4,8,16,24):
    S=[tuple(range(3*i,3*i+3)) for i in range(b) for _ in range(3)]
    pins=tuple(((1<<0)|(1<<(3*i)),0) for i in range(1,b))
    expect=(2**b+1,2**(b+1),(3*2**(b-1),)*(3*b)) if b>13 else None
    run('coupled_'+str(b),S,3*b,(1<<(3*b))-1,pins,expect)
# High-rank nonlinear controls: distinct triples, shared original column bit.
base=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
r0=tuple(sum(1<<j for j,T in enumerate(base) if i in T) for i in range(18));x0=181773997
u,V=chart(30,canon((r,1) for r in r0));w0=tuple((r&x0).bit_count() for r in r0);local=[]
for bit in (0,1):
    T=[lift(u,V,z) for z in range(1<<len(V))];T=[y for y in T if y&1==bit and all((r&y).bit_count()<=a for r,a in zip(r0,w0))]
    local.append((len(T),sum(all((r&y).bit_count()==1 for r in r0) for y in T),tuple(sum((r&y).bit_count()<a for y in T) for r,a in zip(r0,w0))))
for b in (2,3):
    S=[tuple(v+18*i for v in T) for i in range(b) for T in base];x=sum(x0<<(30*i) for i in range(b));pins=tuple((1|(1<<(30*i)),0) for i in range(1,b))
    expect=(sum(c**b for a,c,p in local),sum(a**b for a,c,p in local),tuple(sum(p[e]*a**(b-1) for a,c,p in local) for e in range(18))*b)
    run('nonlinear_coupled_'+str(b),S,18*b,x,pins,expect,cap=13)
P=canon(((7,1),));assert build(3,(7,7,7),P,Budget(10**6),0,0) is None
try:build(3,(7,7,7),P,Budget(0));assert False
except Exhausted:pass
state['refusal_controls']='PASS';save()
print('SUMMARY',len(state['cases']),sum(len(c.get('observations',[])) for c in state['cases']),Counter(c.get('status','OK') for c in state['cases']),flush=True)
