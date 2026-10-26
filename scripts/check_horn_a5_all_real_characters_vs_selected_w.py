#!/usr/bin/env python3
"""Exact A5 ambivalence and generic unitary real-character obstruction.

ORIGINAL MATH: standard A5 representation / character theory;
A5 is ambivalent (each group element is conjugate to its inverse).
SOURCE WORKER: Agda horn #1244 has the Hatcher G->A5 quotient;
Agda neutrino/Wilson #1247 has a SEPARATE W with nonreal Q(zeta3) trace.
This test proves W is NOT in the image of ANY unitary representation
of A5, not merely the usual real three-dimensional icosahedral one.
No physical connection, exact Hatcher horn geometry, or gauge action
is thereby constructed. A5 ambivalence is prior mathematics, not new.
"""
from itertools import permutations
from fractions import Fraction as Q
from collections import Counter

one = tuple(range(5))
def mul(a,b): return tuple(a[b[j]] for j in range(5))
def inv(a): return tuple(a.index(j) for j in range(5))
def sg(a): return (-1)**sum(a[i]>a[j] for i in range(5) for j in range(i+1,5))
def ordg(a):
    z=one
    for k in range(1,61):
        z=mul(a,z)
        if z==one: return k
    raise AssertionError('not A5')
A5=tuple(a for a in permutations(range(5)) if sg(a)==1)
assert len(A5)==60
assert Counter(map(ordg,A5))=={1:1,2:15,3:20,5:24}
conjugator={}
for g in A5:
    target=inv(g)
    candidates=[x for x in A5 if mul(mul(x,g),inv(x))==target]
    assert candidates, ('nonambivalent',g)
    conjugator[g]=min(candidates)
assert len(conjugator)==60
for g,x in conjugator.items():
    assert mul(mul(x,g),inv(x))==inv(g)
print('PASS full 60/60 EXACT A5 inverse-conjugacy witnesses, including both order-five classes')

# If rho:A5 -> U(d), trace(rho(g)) = trace(rho(xgx^-1))
# = trace(rho(g^-1)) = conjugate(trace(rho(g))).
# So *every* unitary A5 character has real trace (all dimensions).
D=181846007130841
b=-Q(19836986431118,D)
assert b!=0
im2=Q(3,4)*b*b
assert im2>0
print('PASS selected other-worker W: exact (Im Tr W)^2 =',im2,'> 0')
print('NO-GO W in image of ANY unitary A5 representation, any dimension')

# A5 images have element orders dividing 1,2,3,5. The nonreal trace
# is already decisive; no inference about order of W is made.
print('BOUNDARY excludes this finite A5 source quotient ONLY; cannot exclude SU3 infinite-image or other finite quotients')
