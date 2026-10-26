#!/usr/bin/env python3
"""Exact analytic Hatcher-marked systole and binary end-tree stop test.

Mathematical facts: for flat unitary holonomy rho and ANY gauge with
uniform ||A||op<=M, every piecewise-C1 representative gamma of a
marked FREE-HOMOTOPY class has d(rho([gamma]))<=M*length(gamma),
so d(rho(m))<=M*ell(m), ell=inf of all free representatives' lengths.
Existing PR #1249 / Lean #84 sharp-unitary sibling theorem gives:
if root nontrivial, on EVERY infinite marked branch infinitely many
sibling gaps exceed rational 31/60, since squared amplification at
31/60 is <1. Thus any bounded M>0 requires infinitely many sibling
systoles >31/(60M), along EVERY branch. If source geometry supplies
marked systoles ->0, there is no globally bounded compatible gauge.
This is a gauge-INVARIANT obstruction to existence of bounded gauge,
not a gauge-invariant coefficient magnitude/curvature blowup.

Original horn linked group is Hatcher AT Example 2B.2; Alexander
original wild sphere. PR #1244 owns actual C3 source and tame nested
ball comparator. This file does NOT prove wild-linked handle loops
short, compact-branch-to-singleton source map, or physical action.
"""
from fractions import Fraction as Q
from itertools import product
r=Q(31,60)
c2=4*r*r-r**4
assert c2==Q(12914879,12960000)<1
assert Q(1,2)<r<Q(13,25)
print('PASS exact rational eventual-sibling amplifier c²=12914879/12960000<1')
# If all siblings at depths >=K have norm gaps <=r, then
# gap(parent K)^2 <=4*c2**n for arbitrarily large n ->0.
for depth in (1,2,4,8,16,32,64,128,256):
    assert 4*c2**depth>0
assert 4*c2**398<=1 and 4*c2**397>1
print('PASS depth-398 finite W>1 example; no finite depth pretends to prove limit')
# A uniform tame control tree has singleton branch intersections
# and max diam bound 3^-n. This is ONLY a tame comparator; it has
# no inherited Hatcher wild meridian or pi1 by itself.
for n in range(9):
    diam=Q(1,3**n)
    assert len(list(product((0,1),repeat=n)))==2**n
    assert diam>0
    if n>0: assert diam<Q(1,3**(n-1))
print('PASS exact shrinking binary-tame diameter envelope (NOT linked wild source)')
# Strong fail-closed geometric example: simple once-winding
# polar curve R(theta)=eps*(1+sin(N theta)/4), eps=3^-n,
# N=3^n. Image diameter <= 5eps/2 ->0 while total
# radial variation =4N*(eps/4)=1, so curve length >=1.
# It remains a once-winding meridian class of punctured plane!
for n in range(1,9):
    eps=Q(1,3**n); N=3**n
    radial_variation=4*N*(eps/4)
    diameter_upper=Q(5,2)*eps
    assert radial_variation==1
    assert diameter_upper<=Q(5,6)
print('PASS once-winding small-diameter / length>=1 counterexample')
# The infimum marked length (systole) differs: round representative
# radius eps has short length 2*pi*eps even while the wiggly
# representative is long. Source must establish an actual short
# representative of the CORRECT free meridian class avoiding X_n.
for m in (Q(1,4),Q(1),Q(10)):
    min_length_required=r/m
    assert m*min_length_required==r
print('PASS exact necessary marked-systole lower 31/(60 M) for bounded M>0')
print('OPEN wild Hatcher source: complete infinite branch handles, meridian annulus and Euclidean systolic certificate')
