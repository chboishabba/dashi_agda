#!/usr/bin/env python3
"""F7 2I^3 rtimes C3 exact central/Fourier projector scope discriminator.

Full actor acts on Omega=C3 x SL2(F5), 360 points.
Central -I acts freely within 180 quotient fibres. C3 acts on the
sector index, and normalizes (but does NOT centralize) 2I^3.
Over F7 there are six rank-60 spectral subspaces under C2 x C3,
but ONLY the spin-even/spin-odd 180+180 split is invariant under
the FULL nonabelian actor. Do not call the six Fourier blocks
full-actor isotypic components or physical Dirac eigensectors.
"""
from itertools import product,combinations
from collections import defaultdict
from random import Random
P=7
I=(1,0,0,1);N=(4,0,0,4)
def mul(a,b):
    x,y,z,w=a;X,Y,Z,W=b
    return ((x*X+y*Z)%5,(x*Y+y*W)%5,(z*X+w*Z)%5,(z*Y+w*W)%5)
def inv(a):
    x,y,z,w=a
    return (w%5,(-y)%5,(-z)%5,x%5)
def comm(a,b):return mul(mul(mul(a,b),inv(a)),inv(b))
def power(a,n):
    v=I
    for _ in range(n):v=mul(v,a)
    return v
def subgroup(gs):
    gs=tuple(gs)+tuple(inv(g) for g in gs)
    seen={I};front=[I]
    while front:
        x=front.pop()
        for g in gs:
            y=mul(x,g)
            if y not in seen:seen.add(y);front.append(y)
    return frozenset(seen)
G=tuple((a,b,c,d) for a,b,c,d in product(range(5),repeat=4)
        if (a*d-b*c)%5==1)
Q=sorted({subgroup((a,b)) for a,b in combinations(
         [g for g in G if power(g,2)==N],2) if comm(a,b)==N},
         key=lambda h:sorted(h))
assert len(G)==120 and len(Q)==5
ix={h:i for i,h in enumerate(Q)}
def project(g):return tuple(ix[frozenset(mul(mul(g,h),inv(g)) for h in H)]
                             for H in Q)
assert len({project(g) for g in G})==60
assert all(sum(project(h)==x for h in G)==2 for x in set(project(g) for g in G))
assert (120**3*3,60**3*3)==(5_184_000,648_000)
assert 5_184_000%P and 648_000%P
slots=tuple((i,g) for i in range(3) for g in G)
assert len(slots)==360
fibres=defaultdict(list)
for x in slots:fibres[(x[0],project(x[1]))].append(x)
assert len(fibres)==180 and all(len(f)==2 for f in fibres.values())
def T(x):return ((x[0]+1)%3,x[1])
def Z(x):return (x[0],mul(N,x[1]))
def Tk(x,j):return ((x[0]+j)%3,x[1])
assert all(T(Z(x))==Z(T(x)) and Z(Z(x))==x for x in slots)
for j,e in product(range(3),range(2)):
    assert sum(Tk(x,j)==(Z(x) if e else x) for x in slots)==(
        360 if j==0 and e==0 else 0)
# Six joint eigensectors: rank 360/(3*2)=60 EACH, but the
# Fourier characters of C3 are only subgroup sectors.
zeta=2
assert pow(zeta,3,P)==1 and pow(zeta,2,P)==4
def plus(*vecs):
    ans={}
    for v in vecs:
        for x,a in v.items():ans[x]=(ans.get(x,0)+a)%P
    return {x:a for x,a in ans.items() if a}
def scale(t,v):return {x:(t*a)%P for x,a in v.items() if (t*a)%P}
def pull(v,f):return {x:v[f(x)] for x in slots if v.get(f(x),0)}
def even(v):return scale(pow(2,-1,P),plus(v,pull(v,Z)))
def odd(v):return scale(pow(2,-1,P),plus(v,scale(-1,pull(v,Z))))
def phase(v,k):
    return scale(pow(3,-1,P),plus(*[
        scale(pow(zeta,(-k*j)%3,P),pull(v,lambda x,j=j:Tk(x,j)))
        for j in range(3)]))
def delta(x):return {x:1}
for x in (slots[0],slots[120],slots[243],slots[-1]):
    v=delta(x)
    assert plus(even(v),odd(v))==v
    assert not even(odd(v)) and not odd(even(v))
    assert plus(*(phase(v,k) for k in range(3)))==v
    for k in range(3):
        assert phase(phase(v,k),k)==phase(v,k)
        assert even(phase(v,k))==phase(even(v),k)
        for h in range(3):
            if k!=h:assert not phase(phase(v,k),h)
# The real full actor is a triple of SL2(F5) components and an
# outer sector phase. Diagonal -I is CENTRAL; pure C3 is not.
def actor(a,x):
    triple,k=a;i,g=x;j=(i+k)%3
    return j,mul(triple[j],g)
def act(v,a):return pull(v,lambda x:actor(a,x))
rng=Random(20261024)
actors=[((I,I,I),k) for k in range(3)]
actors.extend((tuple(rng.choice(G) for _ in range(3)),
               rng.randrange(3)) for _ in range(16))
for a in actors:
    for x in slots:assert actor(a,Z(x))==Z(actor(a,x))
    for x in slots[::29]:
        v=delta(x)
        assert even(act(v,a))==act(even(v),a)
        assert odd(act(v,a))==act(odd(v),a)
nontrivial=next(g for g in G if g!=I)
a=((nontrivial,I,I),0)
counterexample=next((x for x in slots
    if phase(act(delta(x),a),0)!=act(phase(delta(x),0),a)),None)
assert counterexample is not None
print("PASS full spin/projective actors 5184000/648000 Maschke over F7")
print("PASS exactly six C3 x center(C2) joint rank-60 blocks")
print("PASS FULL actor invariant central-sign EVEN/ODD decomposition 180+180")
print("PASS non-equivariance counterexample for C3 Fourier block under FULL actor:",counterexample)
print("NOT CLAIMED: six invariant full-actor irreducibles, Monster sectors, physical zero modes")
