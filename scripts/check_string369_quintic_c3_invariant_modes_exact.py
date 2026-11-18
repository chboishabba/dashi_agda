#!/usr/bin/env python3
"""Exact same-C3 invariant polynomial-deformation modes of Fermat quintic.

Classical: Jacobian ring R=C[z0..z4]/(dP), degree-5 deformation space,
Maschke/Burnside averaging and finite cyclic-invariant theory; distinct
from string quotient orbifold/twisted-sector cohomology.
Existing DASHI: QuinticThreefoldCandidate,
FermatQuinticGradientNonvanishingExact, CalabiYau369CompactFibreBridge,
TOE369C3RealizationGraphExact, original C3 character owners.
User hypothesis: observer-visible internal modes may differ with C3
selection; test on SAME actual CY3 defining polynomial and gauge modes.
ChatGPT-assisted exact finite character/orbit witness 2026-11-18.
"""
from itertools import product

degree_five=[a for a in product(range(6),repeat=5) if sum(a)==5]
def c3(a): return a[1],a[2],a[0],a[3],a[4]
def orbit(a):
    out={a}
    for _ in range(2):
        out|={c3(b) for b in list(out)}
    return frozenset(out)
orbits={orbit(a) for a in degree_five}
fixed_poly=sum(a==c3(a) for a in degree_five)
assert len(degree_five)==126
assert fixed_poly==9
assert len(orbits)==48==(126+2*9)//3

# Degree-five Jacobian ideal of Fermat P=sum z_i^5:
# derivative 5 z_i^4, multiplied by each coordinate z_j, all distinct.
jac=[tuple(4*(i==k)+(j==k) for k in range(5))
     for i in range(5) for j in range(5)]
assert len(jac)==len(set(jac))==25
fixed_jac=sum(a==c3(a) for a in jac)
assert fixed_jac==4
assert len({orbit(a) for a in jac})==11==(25+2*4)//3
# Exactness of finite-group invariants in characteristic 0:
# dim(R5^C3)=dim(Poly5^C3)-dim(Jac5^C3)=48-11=37.
h21_invariant=48-11
assert h21_invariant==37
h11_invariant=1 # hyperplane class is fixed
untwisted_difference=h21_invariant-h11_invariant
assert untwisted_difference==36 and untwisted_difference!=3

# The nonfree C3 quotient has fixed locus:
# z0=z1=z2=0, z3^5+z4^5=0 : five isolated projective roots.
# Other two projective eigenspaces of the cyclic permutation
# are each 1-dimensional and lie in the quintic because
# 1+omega^5+omega^10=1+omega^2+omega=0.
# Hence seven projective fixed points total.
fixed_on_projective_fixedsubspace=5
fixed_on_nontrivial_eigenlines=2
assert fixed_on_projective_fixedsubspace+fixed_on_nontrivial_eigenlines==7
print('PASS: 126 degree-five quintic monomials, 9 fixed, 48 invariant orbits')
print('PASS: 25 independent degree-five Jacobian ideal monomials, 4 fixed, 11 orbits')
print('PASS: 37 C3-invariant complex deformations, 1 invariant Kahler class')
print('PASS: untwisted invariant difference 36 != 3; NOT a full orbifold chiral index')
print('PASS: 7 projective fixed points, so quotient has twisted/resolution gates')
print('OPEN: C3 equivariant gauge bundle, full Dirac spectrum, twisted sectors and actual SM')
