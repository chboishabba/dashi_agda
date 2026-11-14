#!/usr/bin/env python3
"""Agda-side independent finite discriminator: 13 order-three Albert lines.

Original external owners: Robert L. Griess Jr., J. Algebra 131 (1990);
Chen--Lam--Shimakura, Math. Z. 288 (2018) for the SEPARATE
Moonshine VOA Z3 orbifold. This consumes existing DASHI group and
Moonshine source provenance; it DOES NOT create a VOA/Albert intertwiner.

Q-rational cyclic grading restriction:
  source A=(Z/3)^3 has 13 cyclic lines;
  for every nonzero a, the 27 source character grades split into
  9 fixed + 18 nontrivial over Q, and 9+9+9 over Q(omega).
  Two independent phase axes have a 3D fixed intersection;
  three independent axes leave the 1D original Albert identity line.
There is NO full-normalizer-canonical distinguished phase axis.
"""
from itertools import combinations,product
import sympy as s
V=tuple(product(range(3),repeat=3))
neg=lambda v:tuple((-x)%3 for x in v)
dot=lambda u,v:sum(a*b for a,b in zip(u,v))%3
lines=tuple(v for v in V if v!=(0,0,0) and v<neg(v))
assert len(lines)==13
I=s.eye(27)
C=s.Matrix([[0,-1],[1,-1]])
assert C**3==s.eye(2)
def source_unit_phase(a):
    U=I.copy()
    for k,b in enumerate(lines):
        U[1+2*k:3+2*k,1+2*k:3+2*k]=C**dot(a,b)
    return U
def proj(a):
    U=source_unit_phase(a)
    return (I+U+U*U)/3
assert all(sum(dot(a,x)==i for x in V)==9 for a in lines for i in range(3))
for a in lines:
    U=source_unit_phase(a);P=proj(a)
    assert U**3==I and s.trace(U)==0 and s.trace(U**2)==0
    assert P*P==P and s.trace(P)==9
for a,b in combinations(lines,2):
    assert s.trace(proj(a)*proj(b))==3
assert proj((1,0,0))*proj((0,1,0))*proj((0,0,1))==(
    I[:,0]*I[0,:])
# Source normalizer on F3^3 label space, not an independently
# constructed full nonabelian VOA or Albert normalizer action lift.
def determinant3(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            -a[1]*(b[0]*c[2]-b[2]*c[0])
            +a[2]*(b[0]*c[1]-b[1]*c[0]))%3
transports=set();count=0
for rows in product(V,repeat=3):
    if determinant3(*rows)!=1:continue
    count+=1
    v=tuple(row[0] for row in rows)
    transports.add(frozenset((v,neg(v))))
assert count==5616 and transports=={
    frozenset((v,neg(v))) for v in lines}
print('PASS 13 source-Griess C3 lines; Q fixed/other dimensions 9/18')
print('PASS complex scalar extension yields 9/9/9 eigenphase multiplicities')
print('PASS intersection fixed dimensions 9,3,1 and SL3(3) 13-line transitivity')
print('NOT PAID: selected Monster 3B VOA actor, mode, eigenspace or a physical 27-cube')
