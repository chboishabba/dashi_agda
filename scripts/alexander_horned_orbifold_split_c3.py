#!/usr/bin/env python3
"""Finite audit: split orbifold C3 source for the actual geometric rotation.

For any connected open 3-manifold E with a smooth C3 action fixing x0:
E -> E x_{C3} EC3 -> BC3 is a fibre sequence; x0 gives a section.
Since pi2(BC3)=0, fundamental groups yield
  pi1(E x_{C3} EC3) = pi1(E,x0) rtimes C3.

When E is the *source-supported three-wild-ball exterior* and its
geometric pi1 has been identified with G_A*G_A*G_A, this is the
orbifold fundamental group of [E/C3] and it has genuine isotropy C3.
No torsion of the ordinary loop group G_A*G_A*G_A is implied.

Local finite audit: fixed basepoint, 120-element 2I quotient, genuine
semidirect product section and associativity. Not a proof of the
wild-ball construction or Borel-fibration theorem.
"""
from itertools import product
from random import Random

R=lambda p:(p[2],p[0],p[1])
base=(20,20,20)
assert R(base)==base
assert R(R(R((1,2,3))))==(1,2,3)
assert sum(c*c for c in base)>1
sat=((9,0,0),(0,9,0),(0,0,9))
assert all(sum((base[i]-q[i])**2 for i in range(3))>16 for q in sat)
assert min(base)>1 # any tube needs at least two coordinates |x|<=1/4
P=5
e=(1,0,0,1)
def m(a,b):
    x,y,z,w=a;X,Y,Z,W=b
    return ((x*X+y*Z)%P,(x*Y+y*W)%P,(z*X+w*Z)%P,(z*Y+w*W)%P)
G=[(a,b,c,d) for a,b,c,d in product(range(P),repeat=4)
   if (a*d-b*c)%P==1]
assert len(G)==120
I=(e,e,e)
def shift(v,k):return tuple(v[(i-k)%3] for i in range(3))
def product_actor(a,b):
    q,k=a;r,l=b;rs=shift(r,k)
    return tuple(m(q[i],rs[i]) for i in range(3)),(k+l)%3
unit=(I,0)
def section(k):return I,k
rng=Random(20261025)
actors=[unit]+[section(k) for k in range(3)]
actors += [(tuple(rng.choice(G) for _ in range(3)),rng.randrange(3))
           for _ in range(32)]
for x in actors:
    assert product_actor(x,unit)==x==product_actor(unit,x)
    for y in actors:
        assert product_actor(section(x[1]),section(y[1]))==section((x[1]+y[1])%3)
        for z in actors[::5]:
            assert product_actor(product_actor(x,y),z)==product_actor(x,product_actor(y,z))
assert section(1)!=unit
assert product_actor(product_actor(section(1),section(1)),section(1))==unit
print('PASS actual fixed basepoint (20,20,20) outside C3-invariant geometric scaffold')
print('PASS actual (2I)^3 semidirect C3 law, associative, and C3 section')
print('TOPOLOGICAL THEOREM: fixed point splits Borel/orbifold pi1 extension')
print('NOT CLAIMED: torsion in ordinary exterior pi1 or machine-certified wild embedding')
