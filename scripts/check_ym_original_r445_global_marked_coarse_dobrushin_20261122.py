#!/usr/bin/env python3
"""Exact ORIGINAL 4D SU(N) Wilson R445 coarse two-global-affine-mark Dobrushin certificate.

Source: L4 periodic 1024 original fine positive links, 1536 full plaquettes,
64 original even-origin two-link R445 W, 64 Haar V and ALL 896 spectator links.
F,G are two original disjoint y-z normalized Wilson plaquettes at fine sites
(0,0,0,0) and (0,0,0,2), globally one s and one t, |s|,|t| <= 9/100.

Classical Haar disintegration and Föllmer/Dobrushin covariance comparison
are analytical external theorems; the finite exact local run certifies the
source incidence/matrix domination and rigorous rational Neumann tail.
This is only small-beta <=1/144, NOT physical weak coupling CMP119/122 W3.
"""
from itertools import product, combinations
from collections import Counter, defaultdict
from fractions import Fraction as Q
import sympy as sp

L=4
sites=list(product(range(L),repeat=4))
def shift(x,i):
    y=list(x);y[i]=(y[i]+1)%L;return tuple(y)
original={(x,i) for x in sites for i in range(4)}
first=sorted((x,i) for x in sites if all(z%2==0 for z in x) for i in range(4))
pairs={a:frozenset((a,(shift(a[0],a[1]),a[1]))) for a in first}
selected=set().union(*pairs.values())
owner={b:('V',i) for i,p in pairs.items() for b in p}
for b in original-selected:owner[b]=('S',b)
variables=sorted(set(owner.values())); vindex={v:i for i,v in enumerate(variables)}
windex={k:i for i,k in enumerate(first)}
assert (len(original),len(first),len(selected),len(variables))==(1024,64,128,960)

def face(x,i,j):
    return frozenset(((x,i),(shift(x,i),j),(shift(x,j),i),(x,j)))
faces={face(x,i,j) for x in sites for i,j in combinations(range(4),2)}
assert len(faces)==1536
marks=[face((0,0,0,0),1,2),face((0,0,0,2),1,2)]
assert marks[0].isdisjoint(marks[1])
assert {owner[b] for b in marks[0]}.isdisjoint({owner[b] for b in marks[1]})
assert all(len({owner[b] for b in mark})==4 for mark in marks)

nw=[[0]*960 for _ in range(64)];nh=[[0]*960 for _ in range(64)]
m=defaultdict(int);k=defaultdict(int)
direct=[[0]*64 for _ in range(64)];direct_mark=[[0]*64 for _ in range(64)]
for f in faces:
    vv={vindex[owner[b]] for b in f}
    assert len(vv)==4
    for a in vv:
        for b in vv:
            if a!=b:m[a,b]+=1
    active=sorted(f.intersection(first))
    assert len(active)<=2
    for a in active:
        for v in vv:nw[windex[a]][v]+=1
    for a,b in combinations(active,2):
        direct[windex[a]][windex[b]]+=1
        direct[windex[b]][windex[a]]+=1
for f in marks:
    vv={vindex[owner[b]] for b in f}
    for a in vv:
        for b in vv:
            if a!=b:k[a,b]+=1
    active=sorted(f.intersection(first))
    for a in active:
        for v in vv:nh[windex[a]][v]+=1
    for a,b in combinations(active,2):
        direct_mark[windex[a]][windex[b]]+=1
        direct_mark[windex[b]][windex[a]]+=1
assert all(sum(row)==24 for row in nw)
assert all(sum(row)<=4 for row in nh)
assert Counter(sum(row) for row in nh)==Counter({0:60,4:4})
assert all(sum(row)==3 for row in direct)
assert all(sum(row)<=1 for row in direct_mark)
assert all(sum(row)==(36 if variables[i][0]=='V' else 18)
           for i,row in enumerate([None]*960) for row in [[sum(m.get((i,j),0) for j in range(960))]])
assert sum(m.values())==18432
assert len(k)==24 and all(k[key]==1 for key in k)
assert max(sum(k.get((i,j),0) for j in range(960)) for i in range(960))==3
assert max(sum(nw[i][a] for i in range(64)) for a in range(960))==12

# Analytic ar=atanh(9/100)<=r/(1-r^2)<91/1000 (power series).
# Use one COMMON integer denominator for beta, r and overbound ar.
beta=Q(1,144);r=Q(9,100);a_bound=Q(91,1000)
assert r/(1-r*r)<a_bound
DEN=18000
assert beta*DEN==125 and r*DEN==1620 and a_bound*DEN==1638
# Entrywise upper Dobrushin matrix: C <= beta*m + r*k.
T=[{} for _ in range(960)]
for (i,j),count in m.items():T[i][j]=125*count+1620*k.get((i,j),0)
assert max(sum(row.values()) for row in T)==9360
q=Q(9360,DEN);assert q==Q(13,25)

# Exact positive vectors v_i[a]=beta*n_i[a]+a_bound*h_i[a], units 1/DEN.
V=[[125*nw[i][a]+1638*nh[i][a] for a in range(960)] for i in range(64)]
B=[sum(V[i][a] for i in range(64)) for a in range(960)]

# Exact rational Neumann bound D B <= S_N + [q^N/(1-q)] max_a B[a]
# where D=(I-C)^-1. Integer Horner recursion:
# S_N=Z_N/DEN^N and Z_{n+1}=DEN^n B + T Z_n,
# S_N=B/DEN + ... + (T/DEN)^(N-1) B/DEN.
N=16
num=B[:];powden=DEN
for step in range(2,N+1):
    num=[(powden*B[i] + sum(w*num[j] for j,w in T[i].items())) for i in range(960)]
    powden*=DEN
assert powden==DEN**N
bound_tail= q**N/(1-q)*Q(max(B),DEN)

# For each *true* original coarse W_i:
# row <= beta*sum_{j!=i} m_direct_ij
#      + ar*sum_{j!=i} mark_direct_ij
#      + 4 v_i^T D (B-v_i),
# and use positivity D v_i >= v_i to upper-bound the latter by
# 4 v_i^T (D B-v_i), with an EXACT positive rational Neumann tail.
rows=[]
for i in range(64):
    positive=[(a,v) for a,v in enumerate(V[i]) if v]
    direct_val=beta*sum(direct[i])+a_bound*sum(direct_mark[i])
    finite=Q(sum(v*num[a] for a,v in positive),DEN*powden)
    self_lower=Q(sum(v*v for _,v in positive),DEN*DEN)
    tail=Q(sum(v for _,v in positive),DEN)*bound_tail
    row=direct_val+4*(finite-self_lower+tail)
    rows.append(row)

max_row=max(rows)
assert max_row<Q(11,20),('marked coarse row did not contract to <11/20',float(max_row))
assert max_row>Q(1,2) # permits exact 11/20 without falsely claiming 1/2
# TRUE original log-score Hessian direct+covariance negative control.
u,v,lam=sp.symbols('u v lam',real=True)
H=lam*u*v
Z=2*sp.exp(H)
assert sp.simplify(sp.diff(sp.log(Z),u,v)-lam)==0
assert sp.simplify(sp.diff(H,u,v)-lam)==0
# A mixed mark source is not a free per-polymer insertion or zero intrinsic Hessian.
print('PASS original 1024-link, 1536-full-plaquette, 64 native W, 960 true Haar fibre variables')
print('PASS two genuine original disjoint F/G Wilson plaquettes, disjoint conditional supports, four marked coarse W')
print('PASS source rows m=36/18, marked conditional incidence row extra <=3r; q_f<=13/25')
print('PASS ALL 64 exact rational coarse marked rows, Neumann terms=',N,'max=',float(max_row),'certified<11/20')
print('PASS exact rational tail',float(bound_tail),'max',max(B),'out of',DEN)
print('PASS direct shared-face and mark Hessian nonzero control')
print('SCOPE: L4 specified opposite y-z global marks, real |s|,|t|<=9/100, beta<=1/144; no weak-coupling CMP119/122 W3, E1/D2 or Agda')
