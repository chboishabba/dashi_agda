#!/usr/bin/env python3
"""RH P0 original 27=1+26 / 26=9+8+9 geometrical coefficient max-cut.

Exact fractions: q_j(t)*r^(2j) <= E_j, E(z)=(1+z)^9(1+z/4)^9
prod_{k=14,15,17,18}(1+z/k^2)^2; sharp as t->infinity.
The four quartic pole factors are majorized by eight VIRTUAL quadratic
slots, not literally split into real quadratics. Punctured cube is an
ORIENTED indexing chart; not a J/F4/Monster intertwiner, nor RH proof.
"""
from fractions import Fraction as F
from itertools import product
from math import comb

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def product_polys(factors):
    p=[F(1)]
    for f in factors:p=mul(p,f)
    return p

T=(-1,0,1);origin=(0,0,0)
cube=[(x,y,z) for z in T for x in T for y in T if (x,y,z)!=origin]
assert len(cube)==26
assert [sum(v[2]==z for v in cube) for z in T]==[9,8,9]
antipode=lambda p:tuple(-x for x in p)
axes={frozenset((p,antipode(p))) for p in cube}
central=sorted((a for a in axes if all(v[2]==0 for v in a)),key=lambda a:min(a))
assert len(axes)==13 and len(central)==4
freq={a:k for a,k in zip(central,(14,15,17,18))}
weights={}
for p in cube:
    if p[2]==-1:weights[p]=F(1)
    elif p[2]==1:weights[p]=F(1,4)
    else:weights[p]=F(1,freq[frozenset((p,antipode(p)))]**2)
assert all(weights[p]==weights[antipode(p)] for p in cube if p[2]==0)
assert all(weights[p]!=weights[antipode(p)] for p in cube if p[2]!=0)
E=product_polys([[F(1),weights[p]] for p in cube])
assert len(E)==27 and E[0]==1
assert E[1]==F(1294113017,114704100)
assert E[26]==F(1,4469951457296583229440000)
assert all(F(0)<E[j]<=F(comb(26,j)) for j in range(27))
print("PASS original 26 oriented slots, 13 signed pairs, 9+8+9 weights")
print("E1 =",E[1],"E26 =",E[26])

def exact(t):
    r=F(t,16); delta=F(1)/(4*r*r)
    parts=[[F(1),F(1)]]*9+[[F(1),F(1,4)]]*9
    for k in (14,15,17,18):
        m=F(k*k);den=m+delta
        c=F(2)*(m-delta)/(den*den)
        d=F(1)/(den*den)
        assert F(0)<=c<=F(2,k*k) and F(0)<=d<=F(1,k**4)
        parts.append([F(1),c,d])
    q=product_polys(parts)
    assert len(q)==27
    assert all(F(0)<q[j]<=E[j] for j in range(27))
    assert all(q[j]/r**(2*j)<=E[j]/r**(2*j) for j in range(27))
    return q
for t in (200,300,1000,32768,1000000):
    q=exact(t)
    print("PASS",t,"q1*r^2",float(q[1]),"q13*r^26",float(q[13]))
lim=product_polys([[F(1),F(1)]]*9+[[F(1),F(1,4)]]*9+
                  [[F(1),F(2,k*k),F(1,k**4)] for k in (14,15,17,18)])
assert lim==E
assert len({frozenset((j,27-j)) for j in range(1,27)})==13
assert any(E[j]!=E[27-j] for j in range(1,14))
print("PASS sharp coefficientwise t->infinity limit, no spurious palindromicity")
print("T_b,sharp = max(32768,16 max_p,j (208 E_j ||b_p^(2j)||_1)^(1/2j));")
print("OPEN numeric plateau derivative threshold, kernel, full E2/FarExact, independent P0 E3.")
