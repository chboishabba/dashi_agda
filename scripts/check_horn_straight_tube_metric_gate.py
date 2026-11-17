#!/usr/bin/env python3
"""Original Hatcher local Z-A (two straight tubes) meridian metric gate.

Hatcher Example 2B.2: Z-A is HOMEOMORPHIC to an open ball with
TWO straight tubes deleted. Its source meridians generate F2 and
the attaching annulus word is their commutator. This yields no
EUCLIDEAN bi-Lipschitz constant for the homeomorphism from the
straight model into the actual WILD linked-horn satellite.

If one ACTUAL marked local source chart has a metric (Lipschitz)
transport with constant Lambda_n, a transverse round circle of
radius b_n about a straight tube maps to a Hatcher-marked loop
of length at most 2*pi*Lambda_n*b_n, provided the map's image
lies in the TRUE complement with whole-stage avoidance.
These conditions are SOURCE INPUTS, not provided by the demo.

Exact upper pi<22/7 makes the rational cap
(44/7)*Lambda_n*b_n. Under uniform Lambda and b_n->0 this
vanishes. If Lambda_n grows as 3^n with b_n~3^-n, it does NOT.
This isolates the precise metric-vs-homeomorphism obstruction.
"""
from fractions import Fraction as F

selected_flat_child_gap=F(781,1000)
source_sibling_tail_gap=F(31,60)
pi_upper=F(22,7)
for depth in range(9):
    # Synthetic two proper straight tubes at transverse centres
    # +/-2b; radius of physical solid core a=b/2. Round meridian
    # of radius b avoids BOTH local tubes; centre gap=4b>2(b+a).
    b=F(1,5*3**depth); a=b/2
    separation=4*b
    assert a<b and separation > 2*(b+a)
    assert b-a>0
    # Both children have identical LOCAL geometric length 2*pi*b.
    upper_uniform=2*pi_upper*b
    upper_bad_distortion=2*pi_upper*(3**depth)*b
    assert upper_uniform == F(44,35*3**depth)
    assert upper_bad_distortion == F(44,35)
    if depth>=1:
        assert upper_uniform < selected_flat_child_gap
    assert upper_bad_distortion > selected_flat_child_gap
print('PASS exact stage-1..8 round child ML<781/1000 in synthetic Lambda=1 model (M=1)')
print('PASS Lambda_n=3^n with same radii blocks all-depth metric conclusion')

# The infinite nontrivial root along any marked branch forces
# infinitely many actual sibling systoles >31/(60M) for bounded M.
# Uniform distortion with b->0 would violate that; uncontrolled
# distortion is genuinely a remaining source-geometry ambiguity.
for depth in range(1,9):
    assert 2*pi_upper*F(1,5*3**depth) < source_sibling_tail_gap
print('PASS synthetic fast local-sibling metric gate; NOT source Hatcher wild realization')

# Negative control: a homeomorphism can have huge metric distortion.
# Explicit linear stretch S_n(x,y,z)=(3^n*x,y,z) is a genuine
# homeomorphism, with Lipschitz upper 3^n and no uniform bound.
# Thus mere topological homeomorphism does NOT pay metric scaling.
for depth in range(1,9):
    lam=3**depth
    assert lam>1 and lam*F(1,3**depth)==1
print('PASS actual linear homeomorphism family with unbounded source metric distortion')
print('OPEN Lipschitz / bounded-turning real linked Hatcher chart AND induced marked generator map')
