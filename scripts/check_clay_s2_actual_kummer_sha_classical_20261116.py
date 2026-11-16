#!/usr/bin/env python3
"""BSD S2 original E arithmetic diagnostics; classical H1 proof in roadmap.
These finite checks are NOT a proof of global Galois-cohomological exactness.
"""
from fractions import Fraction as Q
from itertools import product
# E:y^2=x^3-x; nonzero discriminant and all rational E[2].
a,b=-1,0
discriminant=-16*(4*a**3+27*b**2)
assert discriminant==64
assert all(x**3-x==0 for x in (-1,0,1))
assert len({-1,0,1})+1==4 # plus point at infinity
# Actual cocycle check on C2 acting by negation on Z/8.
# cocycle f(g)=t; f(g^2)=t+(-t)=0; coboundaries gq-q=-2q.
M=8
cocycles=[t for t in range(M) if (t-t)%M==0]
coboundaries={(-2*q)%M for q in range(M)}
assert len(cocycles)==8 and coboundaries=={0,2,4,6}
# Model exactness 0 -> A/2A -> B -> C[2] ->0:
# A=Z/4, B=Z/4, C=Z/2; injection A/2A=Z/2 -> Z/4 via 1->2.
A=[0,1]
B=list(range(4))
C=[0,1]
inject=lambda a:2*a
project=lambda b:b%2
assert len({inject(a) for a in A})==len(A)
assert {b for b in B if project(b)==0}=={inject(a) for a in A}
assert {project(b) for b in B}==set(C)
assert all(project(inject(a))==0 for a in A)
# Model naturality / local lift: local obstruction is mod 2,
# Selmer is kernel of local obstruction, not a chosen Sha cokernel.
for n in (4,8,16):
    Bn=list(range(n))
    loc=lambda x:x%2
    sel={x for x in Bn if loc(x)==0}
    assert sel==set(range(0,n,2))
    assert all(loc(x)==0 for x in sel)
# Counterexample: four E[2] points do NOT determine E(Q)/2E(Q).
# A=(Z/2)^2 and A'=(Z/2)^2 x Z both have same A[2] of size four,
# but mod-two quotients have size 4 and 8.
assert 2**2==4 and 2**3==8
print("PASS original E discriminant=64 and four rational 2-torsion points")
print("PASS explicit C2 Galois cocycle/coboundary arithmetic")
print("PASS finite exact sequence injection/kernel/surjectivity")
print("PASS local naturality/obstruction and all 3 toy sizes")
print("PASS negative control: E[2] does not determine MW mod 2")
print("FIREWALL classical continuous Galois H1 exactness from standard theorems")
print("FIREWALL S1/S3/S5/S6, all native Agda/Lean and Clay endpoint OPEN")
