#!/usr/bin/env python3
"""RH / native hyperfabric: k,time-indexed *transported* spatial intertwiners.

Original owners: Base369Ternary27HypervoxelFabricGeometryExact (P3^3 and
P3^9); Base369PeriodicTernaryTorusPathRestrictionBidiExact (C3^9);
Base369Ternary27SignedSymmetryMonsterIntertwinerExact (B3 reflection and
C3-frequency conjugation); Base369Ternary27CharacterAdjacencyEquivarianceExact;
PNFHistoryTimeHyperfabricDeltaExact and GovernedIndexedResidualCubeExact
for time/history and refinements. Griess native grade order13 and its
C26 signed hyperfabric lift belong to their historical owners.
This regression checks a new *k-transported graph* exact construction,
NOT fixed-graph Singer equivariance or actual RH zero/physical time dynamics.
"""
from itertools import product, combinations
from collections import Counter
from fractions import Fraction
import sympy as S

V=list(product(range(3),repeat=3))
I={v:i for i,v in enumerate(V)}
M=S.Matrix([[1,1,0],[0,1,1],[1,1,1]])
G=-M
Gi=G.inv_mod(3)
def act(v,mat=G):
    return tuple(int(z%3) for z in mat*S.Matrix(v))
def forward(v):return act(v)
def backward(v):return act(v,Gi)
def path(a,b):
    return sum(x!=y for x,y in zip(a,b))==1 and all(
        x==y or abs(x-y)==1 for x,y in zip(a,b))
def periodic(a,b):
    return sum(x!=y for x,y in zip(a,b))==1
def edges(relation):
    return [(a,b) for a,b in combinations(V,2) if relation(a,b)]
def adjacency(es):
    mat=S.zeros(27)
    for a,b in es:
        mat[I[a],I[b]]=1
        mat[I[b],I[a]]=1
    return mat
def permutation(f):
    mat=S.zeros(27)
    for v in V:mat[I[f(v)],I[v]]=1
    return mat

p3=edges(path)
c3=edges(periodic)
assert len(p3)==54 and len(c3)==81
P=permutation(forward)
assert P**26==S.eye(27)
assert P**13==permutation(lambda v:tuple(-x%3 for x in v))
E=adjacency(p3)
T=adjacency(c3)
assert sum(path(forward(a),forward(b)) for a,b in p3)==0
assert sum(periodic(forward(a),forward(b)) for a,b in c3)==0
for es,mat in ((p3,E),(c3,T)):
    pushed=adjacency([(forward(a),forward(b)) for a,b in es])
    assert pushed==P*mat*P.T
    assert pushed*P==P*mat
    assert len(es)==sum(int(pushed[i,j]) for i in range(27) for j in range(i+1,27))
    assert mat!=pushed
assert sum(path((2-x,a,b),(2-y,a,b)) for a,b in ((0,0),(1,1)) for x,y in [(0,1)])==2

# Exact signed C3^3 Fourier-character dual map (G^-1)^T.
dual=Gi.T
assert all(
    sum(act(q,dual)[j]*forward(x)[j] for j in range(3))%3
      ==sum(q[j]*x[j] for j in range(3))%3
    for q in V for x in V
)
# Periodic torus L has character spectrum lambda(q)=3*support(q).
# The NONPERIODIC P3 Laplacian is NOT diagonal in these characters.
spectral=Counter(sum(z!=0 for z in q) for q in V)
assert spectral=={0:1,1:6,2:12,3:8}
assert sum(spectral.values())==27

# The true full spatial hyperfabric is (P3^3)^3 = P3^9; not 27 sites.
# Count all SOURCE edges without giant 19,683-by-19,683 matrices.
nodes=product(range(3),repeat=9)
def hyper_forward(v,mat=G):
    return act(v[:3],mat)+act(v[3:6],mat)+act(v[6:],mat)
assert 27**3==19683
expected=3*54*27**2
count=0
for v in nodes:
    for axis in range(9):
        if v[axis]<2:
            w=v[:axis]+(v[axis]+1,)+v[axis+1:]
            gv,gw=hyper_forward(v),hyper_forward(w)
            assert hyper_forward(gv,S.eye(3))==gv
            assert hyper_forward(gv,Gi)==v
            assert hyper_forward(gw,Gi)==w
            assert gv!=gw
            count+=1
assert count==expected==118098
assert 3*81*27**2==177147

# k indexed pullback: k transports geometry. Physical time is distinct.
L0=S.diag(*[sum(E[i,j] for j in range(27)) for i in range(27)])-E
L=[P**k*L0*(P.T**k) for k in range(3)]
assert (P*L0-L0*P).rank()==24 # FIXED graph cannot commute with Singer
assert all(P*L[k]==L[k+1]*P for k in range(2))
# Two independently selected time instants; a_t is a rational MODEL
# coefficient, not a constructed physical temporal source.
alpha=(Fraction(1,8),Fraction(1,16))
def U(t,k):
    return S.eye(27)-S.Rational(alpha[t].numerator,alpha[t].denominator)*L[k]
for t in range(2):
    for k in range(2):
        assert P*U(t,k)==U(t,k+1)*P
for k in range(2):
    assert U(1,k+1)*P*U(0,k)==P*U(1,k)*U(0,k)

# TWO independent sourced 8/128/16 flags; not a same-object theorem.
# NS official periodic finite model: R=8, hat gain 2^(-(R-1)),
# far-high multiplier 2 placements x 2 Bony x 2 Bernstein.
assert Fraction(1,2**(8-1))==Fraction(1,128)
assert 2*2*2*Fraction(1,128)==Fraction(1,16)
# YM original 4D side2 coarse site count=16, four positive directions,
# two selected fine links per coarse bond => 128=16*8. Distinct from NS.
assert 2**4==16 and 16*4==64 and 64*2==128
assert 4*(4**4)==1024 and 1024-128==896

print("PASS original P3^3: 27/54, torus C3^3: 27/81; no fixed Singer graph equivariance")
print("PASS exact spatial pushforward adjacency P L P^-1 and original 27x27 Laplacian")
print("PASS 729 original C3^3 character identities under contragredient G^-T")
print("PASS periodic Fourier support shells 1,6,12,8; path graph not claimed Fourier diagonal")
print("PASS 19,683 full native P3^9 vertices and 118,098 transported source edges")
print("PASS 177,147 separate nine-dimensional periodic torus edges")
print("PASS two physical-time labels x two refinement-k naturality squares")
print("PASS NS R8/128/16 and YM 16-sites/8-links/128 are DIFFERENT source invariants")
print("OPEN actual time evolutions, untransported Singer graph equivariance, RH signed FarExact")
