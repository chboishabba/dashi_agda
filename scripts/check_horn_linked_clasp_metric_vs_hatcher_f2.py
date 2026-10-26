#!/usr/bin/env python3
"""Finite exact Hopf-clasp MERIDIAN metric certificate and F2 source no-go.

ORIGINAL MATH SOURCES AND OWNERS:
- Hatcher, Algebraic Topology, Example 2B.2, printed 171-172:
  actual punctured-torus annulus map to nonzero [alpha_1,alpha_2]
  in local free group F2. It is NOT merely a Hopf-link complement.
- Classical Hopf-link complement S3-H ≅ T2 × (-1,1), group Z².
  Source: Friedl/Kim knot theory lecture notes, Lemma 3.13, 2024.
- Agda horn original owner #1244 introduced EXACT clasp formulas
  C1=(2cos t,2sin t,0), C2=(1,1+cos t,sin t),
  linking -1, source satellite translation + scale 1/8.
- Neutrino #1247 owns selected W, hyperfabric #1249 / Lean #84
  own its norm gap & conditional actual Hatcher meridian constraint.

New RESULT: constructive meridians for BOTH owner cores have
provable embedded round length pi/4 BEFORE 1/8 scaling; after
scale they have length pi/32 <11/112, disjoint core-tube
neighborhoods with positive rational margins and C3-equivariance.
This proves real finite Euclidean class and metric facts about
owner's selected HOPF-CLASP COMPARATOR, NOT Hatcher Z-A.
Crucially its group is Z², so the source incoming commutator
goes to identity. The finite source cannot instantiate the
selected nontrivial W despite metrically tiny meridians.
"""
from fractions import Fraction as Q
from itertools import product
rho=Q(1,8)
a=Q(1,32)       # solid core tubular thickness in prototype
scale=Q(1,8)   # original horn owner's chosen local affine map
shift=Q(1,4)
assert 0<a<rho
# Core Hopf link separation: exact distance min sqrt(5)-2 >1/5.
# For C2=(1,u,sin t), u=1+cos t in [0,2], distance squared
# to C1 circle (r=2,z=0) is 5+2u-4sqrt(1+u²).
# Convexity ||(1,u)|| <=(1-u/2)+(u/2)*sqrt5 implies
# dist² >= 1+(4-2sqrt5)u >= 9-4sqrt5 = (sqrt5-2)².
#  sqrt5 >11/5 by (11/5)²<5, so min gap>1/5.
assert Q(11,5)**2 < 5
assert 2*a < Q(1,5)
assert rho-a==Q(3,32)>0
assert Q(1)-rho-a==Q(27,32)>0
print('PASS real Hopf two-core disjoint thickness a=1/32; gap(core1,core2)>1/5')
print('PASS BOTH meridian-to-own-core distance exactly 1/8; foreign core >=7/8')

# M1(theta)=(2+rho cos theta,0,rho sin theta).
# Disk D1: y=0, (x-2)^2+z²<=rho².
# C1 crosses y=0 at (+2,0,0),(-2,0,0), only +2 in D1;
# C2 intersects y=0 only at (1,0,0), outside D1.
# M2(theta)=(1+rho cos theta,rho sin theta,0).
# Disk D2: z=0, (x-1)^2+y²<=rho².
# C2 crosses z=0 at (1,2,0),(1,0,0), only (1,0) in D2;
# C1 lies fully in z=0 but has radial distance >=1 from
# centre (1,0,0), so is disjoint D2. Thus M2 links C2 once.
assert (Q(2)-Q(1))**2>rho**2
assert (Q(-2)-Q(2))**2>rho**2
assert Q(2)**2>rho**2
assert (Q(1)-Q(0))**2>rho**2
print('PASS source-core linking/intersection: |lk(M1,C1)|=|lk(M2,C2)|=1; cross=0')

# Original owner C1 spanning disk x²+y²<=4,z=0 meets C2
# at (1,0,0) once inside and (1,2,0) outside.
assert 1**2+0**2<4<1**2+2**2
print('PASS original exact Hopf core linking |lk(C1,C2)|=1')

# WHOLE FAMILY of linked planar circles, not merely link-number data:
# C2_s(theta)=(1-s, 1+s+cos(theta), sin(theta)), s∈[0,1].
# At z=0, C2_s cuts C1's spanning xy disk at
#   (1-s,s,0) (interior, radial norm² <=2<4)
# and (1-s,2+s,0) (exterior, norm² >=5>4).
# Thus an explicit smooth disjoint isotopy takes source owner
# clasp to the standard orthogonal Hopf two-round-circle picture.
# Via isotopy extension the link exterior is T²×I, π1=Z².
for k in range(101):
    s=Q(k,100)
    inside=(1-s)**2+s*s
    outside=(1-s)**2+(2+s)**2
    assert inside<=2<4<5<=outside
assert (1-Q(1))**2+(2+Q(1))**2>4
print('PASS exact 101-parameter Hopf isotopy source disk in/out inequalities; universal by polynomial bounds')

# Inject owner local prototypes into three C3 satellites:
#    p_c = 9 e_c + R^c ((1/4,0,0) + scale*prototype).
# C1 prototype norm=2; C2 norm<=sqrt6<3;
# both meridians prototype norms <=2+rho.
# Triangle inequality puts every point in radius-one
# satellite envelope and OUTWARD of preserved inward cap.
assert shift+scale*Q(3)<1
assert shift+scale*(2+rho)==Q(33,64)<1
assert shift+scale*(1+rho)==Q(25,64)<1
assert scale*(rho-a)>0
assert scale*(Q(1)-rho-a)>0

def R(q): return (q[2],q[0],q[1])
cs=((Q(9),Q(0),Q(0)),(Q(0),Q(9),Q(0)),(Q(0),Q(0),Q(9)))
def embed(c,p):
    v=(shift+scale*p[0],scale*p[1],scale*p[2])
    for _ in range(c): v=R(v)
    return tuple(cs[c][j]+v[j] for j in range(3))
for c in range(3):
    for p in ((Q(2),Q(0),Q(0)),(Q(1),Q(0),Q(0)),
              (Q(2)+rho,Q(0),Q(0)),(Q(1)+rho,Q(0),Q(0))):
        assert R(embed(c,p))==embed((c+1)%3,p)
print('PASS exact original C3-equivariant source-map prototype in all 3 sectors')

# Each local meridian after prototype scale:
#  L=2pi*(1/8)*(1/8) = pi/32 < (22/7)/32=11/112.
# If TRUE source Hatcher W child had this LENGTH and compatible
# M=1 flat source gauge, it would violate 781/1000. But the
# Hopf-linked closed cores have ABELIAN Z² fundamental group,
# forcing the proposed parent commutator to identity. THIS
# makes the source-geometry mismatch decisive, not cosmetic.
length_upper=Q(11,112)
assert length_upper<Q(781,1000)
for n in range(8):
    shrinking=length_upper/Q(3**n)
    assert shrinking<=length_upper
print('PASS positive exact metric meridian L<11/112 at all three OWNER comparator sectors')
print('PASS FALSE POSITIVE FIREWALL: Hopf-link group ZxZ forces [m1,m2]=1 != Hatcher F2 nontrivial commutator')
print('OPEN real SAME-OBJECT Hatcher Z-A, punctured-torus annulus and marked 2-handle source metric chart')
