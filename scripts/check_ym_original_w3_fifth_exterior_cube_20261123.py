#!/usr/bin/env python3
"""Original Wilson L4/d2: first exterior restoration at order five.

Exhaustive native face/link support (NOT a finite-group replacement for SU(N)),
exact Q8 Schur-orthogonality negative/positive control, and symbolic cumulant.
No tau>0 uniform estimate, Agda kernel receipt, or CMP119/122 identification.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
import sympy as s

L, d, a, b = 4, 2, 1, 2

def shift(x, axis):
    y = list(x)
    y[axis] = (y[axis]+1) % L
    return tuple(y)

def face(x, i, j):
    return (x, min(i,j), max(i,j))

def boundary(p):
    x,i,j = p
    return frozenset(((x,i),(x,j),(shift(x,i),j),(shift(x,j),i)))

faces = {(x,i,j) for x in product(range(L),repeat=4)
         for i,j in combinations(range(4),2)}
walls = set()
for k in range(d):
    for axis, transverse in ((a,b),(b,a)):
        for offset in (0,1):
            x=[0]*4
            x[0],x[transverse]=k,offset
            walls.add(face(tuple(x),0,axis))
sections={face((k,0,0,0),a,b) for k in range(d+1)}
B=walls|sections
E=faces-B
links=set().union(*(boundary(p) for p in B))
outside={p:boundary(p)-links for p in E}
assert len(faces)==1536 and len(walls)==8 and len(sections)==3
assert Counter(map(len,outside.values())) == Counter({3:76,4:1449})
print("PASS genuine L4/d2: 1525 exterior faces (76 with 3, 1449 with 4 outside links)")

link_faces=defaultdict(set)
for p,edges in outside.items():
    for edge in edges:
        link_faces[edge].add(p)
seeds={p for p in E if boundary(p)&links}

# Search every connected no-private-link external support up to 5 faces.
# A connected candidate contributing with tube marks must begin adjacent to B.
# At any stage a dangling external edge must be covered by a future face.
solutions=defaultdict(set)
visited=set()
def grow(S,incidence):
    dangling=[e for e,n in incidence.items() if n==1]
    if not dangling:
        solutions[len(S)].add(S)
        return
    if len(S)==5:
        return
    e=min(dangling,key=lambda e:len(link_faces[e]-S))
    for p in link_faces[e]-S:
        nextS=S|{p}
        if nextS in visited:
            continue
        visited.add(nextS)
        counts=incidence.copy()
        for link in outside[p]:
            counts[link]+=1
        grow(nextS,counts)

for p in seeds:
    seed=frozenset((p,))
    visited.add(seed)
    grow(seed,Counter(outside[p]))
assert all(not solutions[k] for k in range(1,5))
assert len(solutions[5])==32
print("PASS no-private-link support: 0 for 1..4 distinct exterior faces; 32 for 5")

# A native elementary cube has exactly six native boundary plaquettes.
cubes={}
for x in product(range(L),repeat=4):
    for directions in combinations(range(4),3):
        six=set()
        for i,j in combinations(directions,2):
            other=next(k for k in directions if k not in (i,j))
            six|={face(x,i,j),face(shift(x,other),i,j)}
        cubes[(x,directions)]=frozenset(six)
assert Counter(len(c&B) for c in cubes.values())==Counter({0:990,1:32,6:2})
attached=Counter()
for cube in cubes.values():
    existing=cube&B
    if len(existing)==1:
        q=next(iter(existing))
        assert frozenset(cube-B) in solutions[5]
        attached[q]+=1
assert {frozenset(c-B) for c in cubes.values() if len(c&B)==1} == solutions[5]
assert all(attached[w]==3 for w in walls)
assert [attached[face((k,0,0,0),a,b)] for k in range(3)]==[3,2,3]
assert sum(attached[w] for w in walls)==24
assert sum(attached[h] for h in sections)==8
print("PASS exactly 32 cube candidates: 24 wall (3 each), 8 section (3,2,3)")

# Independent exact Schur-orthogonality regression on Q8 subgroup SU(2).
# Gauge four cube vertical edges to unity; average over four top-edge links.
Q=[(sign,unit) for sign in (1,-1) for unit in range(4)]
mult={(1,2):(1,3),(2,3):(1,1),(3,1):(1,2),
      (2,1):(-1,3),(3,2):(-1,1),(1,3):(-1,2)}
def qmul(A,B):
    x,i=A; y,j=B
    if i==0: return (x*y,j)
    if j==0: return (x*y,i)
    if i==j:return (-x*y,0)
    sign,k=mult[(i,j)]
    return (x*y*sign,k)
def qinv(A):
    x,i=A
    return A if i==0 else (-x,i)
def qt(A):
    return A[0] if A[1]==0 else 0
def qproduct(xs):
    out=(1,0)
    for x in xs:out=qmul(out,x)
    return out

for boundary_element in Q:
    total=0
    for x,y,z,w in product(Q,repeat=4):
        side=qt(x)*qt(y)*qt(z)*qt(w)
        if side:
            total+=side*qt(qproduct((boundary_element,x,y,qinv(z),qinv(w))))
    assert Fraction(total,8**4)==Fraction(qt(boundary_element),256)
print("PASS Q8 exact eight-boundary disk integrals: v2^4 = 1/256")

# For continuous SU(N), t is the real fundamental character and Schur
# orthogonality yields integral t(AU)t(U^-1 B) dH = v_N t(AB).
# Four consecutive gluing integrations yield the genuine cube factor v_N^4.
# A proper subset of the five faces has a private Haar link, so its
# moments vanish with any subset of {F,G}. The seven-point connected
# cumulant is v_N^4*kappa(F,G,t_q).
v,h,m,mp,beta=s.symbols("v h m mp beta")
wall_count=sum(attached[w] for w in walls)
section_count=sum(attached[t] for t in sections)
coefficient=s.factor(beta**5*v**4*(wall_count*v*mp*m**7+
                                     section_count*h*m**8))
expected=beta**5*v**4*(24*v*mp*m**7+8*h*m**8)
assert s.simplify(coefficient-expected)==0
su2=s.factor(coefficient.subs({v:s.Rational(1,4),h:0}))
su3=s.factor(coefficient.subs({v:s.Rational(1,18),h:s.Rational(1,108)}))
assert su2==3*beta**5*m**7*mp/128
assert su3==beta**5*(s.Rational(4,3)*mp*m**7+
                        s.Rational(2,27)*m**8)/104976
print("PASS continuous-SU(N) character identity applied symbolically")
print("FIFTH EXTERIOR TAYLOR COEFFICIENT =",coefficient)
print("SU2 =",su2)
print("SU3 =",su3)
print("FIFTH EXTERIOR DERIVATIVE = 120 * coefficient")
print("OPEN full fifth jet (including sections), all tau>0 absolute W3, CMP119/122")
