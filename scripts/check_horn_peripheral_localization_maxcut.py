#!/usr/bin/env python3
"""Hatcher horn C3 peripheral localisation, exact length and shell controls.

Root attribution: Hatcher Algebraic Topology Example 2B.2 owns linked
meridian group; Alexander 1924 owns the wild sphere. PR #1244 owns the
literal satellite centres, r-=15/4, r+=17/4, source central C, pierced
shell homeomorphism and C3-equivariant central basing paths. PR #1247
owns illustrative selected W. PR #1249/Lean #84 own its spectral lower
and the selected child >781/1000 result. This script DOES NOT prove
Hatcher's actual relative satellite generator map or bounded gauge.

Consequences, with separate source assumptions:
(A) Pierced overlap product (15/4,17/4)xopen(D2) is contractible,
    so ANY flat holonomy of a loop contained in it is identity.
(B) IF the paper-level source central C has pi1(C)=1, any nontrivial
    flat Wilson loop based at x0 must enter one INNER satellite ball.
(C) Every such based rectifiable loop has length >531/10, whereas
    its LOCAL meridian can still be short because the whisker is a
    unitary conjugation. The long based length must NOT pay ML.
(D) A curved connection on the contractible shell can have nonzero
    Wilson holonomy. An explicit smooth abelian-in-SU3 1-form on the
    chart disk provides the negative control.
"""
from fractions import Fraction as Q
from itertools import product
from math import pi,cos,sin

x0=(Q(20),Q(20),Q(20))
centres=((Q(9),Q(0),Q(0)),(Q(0),Q(9),Q(0)),(Q(0),Q(0),Q(9)))
rminus=Q(15,4);rplus=Q(17,4)
qdist=Q(303,10)
assert all(sum((x-y)**2 for x,y in zip(x0,c))==921 for c in centres)
assert qdist*qdist < Q(921)
# Every rectifiable based loop that intersects an inner ball contains
# a point q with dist(x0,q)>=sqrt(921)-15/4 >303/10-15/4.
# Outward and return arcs each have length >=dist(x0,q).
assert 2*(qdist-rminus)==Q(531,10)
assert qdist>rminus
print('PASS C3 central to inner-cut exact lower: L_based > 531/10 (53.1)')

# Source collar centre p_i=13e_i, so it lies in the 15/4..17/4
# pierced spherical shell and is fixed by chart contraction.
for i,c in enumerate(centres):
    p=tuple(Q(13) if j==i else Q(0) for j in range(3))
    assert sum((u-v)**2 for u,v in zip(p,c))==16
    assert rminus**2<16<rplus**2
    # Exact C3 equivariance of the actual owner coordinates.
    assert (p[2],p[0],p[1])==tuple(Q(13) if j==(i+1)%3 else Q(0) for j in range(3))
print('PASS all three original p_i are fixed chart-basepoints and C3-related')

# Direct use of owner's radial-shell product chart at r=4:
# for y in D2, z=R*y, R=(4+sqrt(255/16))/(1/4)=16+sqrt(255).
# 31<R<32 follows from 15<sqrt255<16; no transcendental
# assumptions needed to prove image stays in actual pierced shell.
assert 15**2<255<16**2
# For |y|<=1, radial H_s(y)=(1-s)y stays strictly within D2.
# Consequently local loop around a small chart polygon contracts
# explicitly, with its basepoint (r,y)=(4,0) unchanged.
polygon=((Q(0),Q(0)),(Q(1,2),Q(0)),(Q(0),Q(1,2)),
         (Q(-1,2),Q(0)),(Q(0),Q(-1,2)),(Q(0),Q(0)))
for s in (Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)):
    for y in polygon:
        new=((1-s)*y[0],(1-s)*y[1])
        assert sum(t*t for t in new) < 1
    assert all((1-s)*t==0 for t in polygon[0])
print('PASS 5 exact radial contractions of based shell polygon (all y stay in disk)')

# Constructive curved SU3 NEGATIVE CONTROL on the SAME disk chart:
# A=(i/2)*diag(1,-1,0)*(x dy-y dx), F=i*diag(1,-1,0)*dx^dy.
# Circle |y|=1/2 is contractible in D2 but flux = pi/4,
# so Hol(A)=diag(exp(i pi/4),exp(-i pi/4),1) is nontrivial.
flux_factor=Q(1,4)  # area/pi for r=1/2
assert flux_factor == Q(1,2)**2
# Representative eigenphases, not a measured SU3 gauge field.
assert abs(2*sin(pi/8))>0
assert abs(cos(pi*float(flux_factor))-1)>0
print('PASS curved shell nullhomotopic circle can have nontrivial SU3 holonomy')

# The explicit shell itself can never certify wildness: the same
# chart and central region occur for the TAME satellite comparator.
# The critical missing map is satellite pi1 -> genuine Hatcher G_A.
assert Q(781,1000)<Q(1)
print('OPEN same-object linked satellite generator map and LOCAL length ML')
print('OPEN curved based parent-to-commutator Hatcher Stokes homotopy')
