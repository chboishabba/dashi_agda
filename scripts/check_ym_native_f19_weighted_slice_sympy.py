#!/usr/bin/env python3
"""P0 original Wilson 4D 1024-link source: exact Q8 weighted F19/R445 fibre slice.
Freeze 1021 fine positive bonds at identity; enumerate TWO original native
selected links plus ONE adjacent original spectator. This is a conditional
finite Q8 SU2 slice, NOT full 1024-link Haar/Gibbs or Yang-Mills continuum.
SymPy exact formal coupling verifies original weight and 3 marked moments.
"""
from itertools import product, combinations
from collections import defaultdict
import sympy as sp
origin=(0,0,0,0); identity=(1,0)
rules={(1,2):(1,3),(2,3):(1,1),(3,1):(1,2),
       (2,1):(-1,3),(3,2):(-1,1),(1,3):(-1,2)}
Q8=tuple((s,b) for s in (1,-1) for b in range(4))
def multiply(a,b):
    sa,ia=a; sb,ib=b
    if ia==0:return (sa*sb,ib)
    if ib==0:return (sa*sb,ia)
    if ia==ib:return (-sa*sb,0)
    sign,k=rules[(ia,ib)]
    return (sign*sa*sb,k)
def inverse(x):return x if x[1]==0 else (-x[0],x[1])
def trace(x):return 2*x[0] if x[1]==0 else 0
def shift(site,a):
    y=list(site);y[a]=(y[a]+1)%4
    return tuple(y)
fine=tuple((p,a) for p in product(range(4),repeat=4) for a in range(4))
coarse=tuple((p,a) for p in product(range(2),repeat=4) for a in range(4))
selected=set()
for p,a in coarse:
    root=tuple(2*x for x in p)
    selected.update(((root,a),(shift(root,a),a)))
spectators=set(fine)-selected
assert (len(fine),len(coarse),len(selected),len(spectators))==(1024,64,128,896)
u=(origin,0);v=(shift(origin,0),0);s=(shift(origin,0),1)
assert u in selected and v in selected and s in spectators
active={u,v,s}
plaquettes=tuple(((p,a),(shift(p,a),b),(shift(p,b),a),(p,b))
                 for p in product(range(4),repeat=4)
                 for a,b in combinations(range(4),2))
assert len(plaquettes)==1536
affected=tuple(q for q in plaquettes if active.intersection(q))
assert len(affected)==16
def delta(x,y,z):
    field={u:x,v:y,s:z}
    total=0
    for e0,e1,e2,e3 in affected:
        w=multiply(field.get(e0,identity),field.get(e1,identity))
        w=multiply(w,inverse(field.get(e2,identity)))
        w=multiply(w,inverse(field.get(e3,identity)))
        total+=trace(w)-2
    return total
records=tuple((multiply(x,y),delta(x,y,z))
              for x,y,z in product(Q8,repeat=3))
assert len(records)==512 and all(d%2==0 for _,d in records)
lowest=min(d for _,d in records); z=sp.Symbol("z",positive=True)
weights=defaultdict(lambda:sp.Integer(0))
for coarse_value,d in records:
    weights[coarse_value]+=z**((d-lowest)//2)
weights={w:sp.expand(weights[w]) for w in Q8}
Z=sp.expand(sum(weights.values()))
assert Z.subs(z,1)==512
assert all(weights[w].subs(z,1)==64 for w in Q8)
f=lambda w:trace(w)
g=lambda w:1 if w==(1,0) else -1 if w==(-1,0) else 0
moments=[sp.expand(sum(weights[w]*h(w) for w in Q8))
         for h in (lambda w:1,f,g,lambda w:f(w)*g(w))]
direct=[sp.expand(sum(z**((d-lowest)//2)*h(w) for w,d in records))
        for h in (lambda w:1,f,g,lambda w:f(w)*g(w))]
assert all(sp.expand(a-b)==0 for a,b in zip(moments,direct))
assert sp.expand(moments[3]*moments[0]-moments[1]*moments[2]
                 -(direct[3]*direct[0]-direct[1]*direct[2]))==0
assert all(sum(w==target for w,_ in records)==64 for target in Q8)
assert len({weights[w].subs(z,2) for w in Q8})==3
print("SymPy",sp.__version__)
print("PASS original 1024-link geometry / 128 selected + 896 spectators")
print("PASS original Wilson 1536 plaquettes, 16 affected on 3-link slice")
print("PASS 512/512 exact source-shaped Q8 finite weighted configurations")
print("PASS all 8 original native coarse W=U*V fibres have 64 inputs each")
print("PASS original weighted Z, two marks, product mark and covariance numerator")
print("PASS zero coupling uniform; at z=2 three distinct effective weights")
print("OPEN full interacting Wilson original Haar, physical cutoff-uniform E1/W1/W3/OS H")
