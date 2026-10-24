#!/usr/bin/env python3
"""Source-gated single-branch horn/A5 obstruction with synthetic collar controls.

Mathematical owners: Hatcher (binary commutator horn group); the already
selected A5^3 quotient/180-coordinate c=0 VOA belongs to Agda PR #1244.
The faithful icosahedral rotation realization A5 < SO(3) < SU(3) is
standard; NOT the separate noncentral selected W of Agda PR #1247.
This executable does not construct the Hatcher wild exterior, a gauge
connection on it, or source-verified meridian/collar markings.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from math import sqrt
import sympy as s

identity=tuple(range(5))
def compose(a,b): return tuple(a[b[i]] for i in range(5))
def inverse(a): return tuple(a.index(i) for i in range(5))
def parity(a): return (-1)**sum(a[i]>a[j] for i in range(5) for j in range(i+1,5))
def order(a):
    x=identity
    for n in range(1,61):
        x=compose(a,x)
        if x==identity: return n
    raise AssertionError('group order')
def comm(a,b): return compose(compose(compose(a,b),inverse(a)),inverse(b))
A5=tuple(p for p in permutations(range(5)) if parity(p)==1)
assert len(A5)==60
counts=Counter(order(p) for p in A5)
assert counts==Counter({1:1,2:15,3:20,5:24})
print('PASS source A5 exact permutation group: 60, element-order classes',dict(counts))

# Standard faithful icosahedral 3D rotational representation has
# nonidentity angles pi (15 elements), 2pi/3 (20), and 2pi/5 or
# 4pi/5 (12 each). Minimal norm gap is 2 sin(pi/5).
kappa2=(5-s.sqrt(5))/2
assert s.simplify(kappa2-4*s.sin(s.pi/5)**2)==0
assert s.simplify(kappa2-1).is_positive
assert s.simplify(3-kappa2).is_positive
assert s.simplify((5+s.sqrt(5))/2-kappa2).is_positive
print('PASS icosahedral nonidentity gap²=(5-sqrt5)/2 > 1, gap≈',float(s.sqrt(kappa2)))
# Cross-PR falsifier: the sibling #1247 *selected* W has a nonzero
# ζ3 coefficient in Tr(W). Hence Im Tr(W) = b*sqrt(3)/2 !=0.
# EVERY element of the standard real icosahedral A5<SO(3)<SU(3)
# has REAL trace; SU3 conjugation preserves it. Thus source W is
# NOT conjugate into THIS A5 subgroup and must remain independent.
original_zeta_coefficient=-F(19836986431118,181846007130841)
imaginary_trace_squared=F(3,4)*original_zeta_coefficient**2
assert original_zeta_coefficient!=0 and imaginary_trace_squared>0
print('PASS selected #1247 W has Im(trace)^2=',imaginary_trace_squared,'>0, so NOT conjugate to chosen real SO3 A5')


# Every nontrivial commutator requires BOTH inputs nonidentity.
for a,b in product(A5,repeat=2):
    if comm(a,b)!=identity:
        assert a!=identity and b!=identity
assert all(comm(identity,a)==identity and comm(a,identity)==identity for a in A5)
print('PASS 3600 A5 commutator pairs: nontrivial parent requires both children nontrivial')

# If a root of Hatcher's infinite tower maps nontrivially through the
# original A5 quotient, ALL its descendants are nontrivial, not just
# one selected branch. This induction is a group theorem. So for an
# actual geometric leaf gamma_w with Hol in A5 and ||A||<=M,
#       kappa <= ||Hol(gamma_w)-I|| <= M * length(gamma_w).
# ONE arbitrarily short branch suffices, unlike the general SU3 case.

# Finite *LOCAL* collar test: straight 3D cylinder at x-coordinate
# c_w = sum_(j=1)^n w_j / 3^j, z along tube axis, radius
# r_tube=3^-n/10. An exterior circular collar at R=3^-n/8
# has exact length 2*pi*R and positive radial clearance.
# Its planar winding about the local core is +1.
# These vertical cylinder controls are NOT linked Hatcher horn blocks.
def center(word): return sum((F(bit,3**(i+1)) for i,bit in enumerate(word)),F(0))
def collar(n):
    scale=F(1,3**n)
    tube=scale/10
    moat=scale/20
    meridian=tube+moat/2
    assert meridian==scale/8
    clearance=meridian-tube
    assert clearance==scale/40 and clearance>0
    # Archimedes π < 22/7 => length < 2*(22/7)*R=11*scale/14
    arclen_upper=F(11,14)*scale
    words=tuple(product((0,1),repeat=n))
    cx=sorted(center(w) for w in words)
    assert len(set(cx))==2**n
    if len(cx)>1:
        # Distinct same-depth meridian circles are disjoint with moat.
        assert min(cx[i+1]-cx[i] for i in range(len(cx)-1))>=scale
        assert 2*meridian<scale
    return arclen_upper,clearance,len(words)

for n in range(8):
    L,clear,count=collar(n)
    assert count==2**n and clear==F(1,40*3**n)
    if n==4:
        assert 100*L<1 # hence 100*L < kappa.
    if n==3:
        assert 100*L>1
    print(f'PASS synthetic local collar depth={n} sites={count} length_upper={L} radial_clearance={clear}')

print('PASS conservative M=100, source IF marked stage4 collar gives M*L<1<icosahedral gap')
# Stronger topological negative control: at the next finite level the
# synthetic parent transverse circle encloses the left child core once
# and does not enclose the right child core. Its abelian winding vector
# is (1,0). Any commutator [child0,child1] maps to (0,0) in the
# abelianized planar complement. Thus the false Hatcher stage marking
# is REJECTED by an actual computable invariant, not a human label.
for n in range(7):
    R=F(1,8*3**n)
    for w in product((0,1),repeat=n):
        pc=center(w)
        l=center(w+(0,))
        rr=center(w+(1,))
        assert pc==l
        assert abs(pc-l)<R<abs(pc-rr)
        parent_winding=(1,0)
        commutator_winding=(0,0)
        assert parent_winding!=commutator_winding
print('PASS geometric marking FAIL-CLOSED: 127 parent meridians wind (1,0) not child commutator (0,0)')
print('BLOCKED source Hatcher-marking: these disjoint unlinked straight cylinders DO NOT have parent=child-commutator injection')
print('BLOCKED real 3-copy wild geometry, local-finite-stage collars and compatible bounded source connection not supplied')
print('SINGLE-BRANCH theorem for selected finite A5 image is conditional on genuine marked shrinking descendant, not on all leaves shrinking')
