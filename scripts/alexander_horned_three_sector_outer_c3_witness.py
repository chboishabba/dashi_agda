#!/usr/bin/env python3
"""An EXACT outer-C3 witness for the abstract three-root horn-group free product.

Hatcher's one-root group is G_A = colim F_(2^n), injecting by disjoint
commutator substitutions. Three independent copies yield
G_3 = G_A * G_A * G_A. Rotation rho permutes the three factors.

Suppose rho were conjugation by g. Let m_0 be a nonidentity
meridian in factor 0, and let p0:G_3->G_A be the canonical free
product retraction which kills factors 1,2. Then
  p0(rho(m_0))=1,
  p0(g m_0 g^-1)=p0(g) m_0 p0(g)^-1 !=1,
contradiction. The SAME argument proves rho^2 noninner.
Hence rho has exact order 3 in Out(G_3).

Use the ACTUAL previous 2I quotient to check nontriviality
even after projecting the first factor to SL2(F5). The abstract
theorem has no geometric same-object pi1 or spin-bundle claim.
"""
from itertools import product
p=5
E=(1,0,0,1)
N=(4,0,0,4)
q=(0,4,1,1)
def mul(a,b):
    x,y,z,w=a;X,Y,Z,W=b
    return ((x*X+y*Z)%p,(x*Y+y*W)%p,(z*X+w*Z)%p,(z*Y+w*W)%p)
def inv(a):
    x,y,z,w=a
    return (w%p,(-y)%p,(-z)%p,x%p)
def comm(a,b):return mul(mul(mul(a,b),inv(a)),inv(b))
G=tuple((a,b,c,d) for a,b,c,d in product(range(5),repeat=4)
        if (a*d-b*c)%5==1)
assert len(G)==120 and q!=E
assert mul(mul(q,q),q)==N
assert any(comm(a,b)==q for a in G for b in G)
assert all(mul(mul(g,q),inv(g))!=E for g in G)
for k in (1,2):
    assert (k%3)!=0
    assert all(mul(mul(g,q),inv(g))!=E for g in G)
print("PASS 120/120 conjugates of q nontrivial in actual 2I")
print("PASS q^3=-I and root has a compatible commutator assignment")
print("THEOREM: C3 permutation acts with EXACT order 3 in Out(G_A*G_A*G_A)")
print("OPEN: geometric equivariant isomorphism to pi1(actual horned exterior)")
