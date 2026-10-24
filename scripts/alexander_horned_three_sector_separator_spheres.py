#!/usr/bin/env python3
"""C3-symmetric separating-sphere geometry: exact rational certificates.

Existing ownership:
  scripts/alexander_horned_clopen_tree_handle_scaffold.py:
    corrected t in [1/2,17/2], radius 1/4 tube.
  Docs/topology/AlexanderHornedThreeSectorGeometricVanKampenMaxCut20261024.md:
    source abstract GA*GA*GA, not the finite (2I)^3 quotient.

Let B_i be any compact subset of the unit reference ball centred 9e_i.
Let the connector contain the ACTUAL entire radius-1/4 cylinder along
t e_i for t in [1/2,17/2], and have no other geometry outside the
central/satellite balls (the supported wild B_i must agree with its
standard tame round cap at the inward attachment).

The separating sphere S_i={|x-9e_i|=4} intersects that connector
in exactly a transverse DISK. On S_i the cylinder intersection is
parametrized by (u,v) in u^2+v^2 <=1/16 via
  (t,u,v)=(9-sqrt(16-u^2-v^2),u,v),
with cyclically permuted coordinates for sector i.

Thus S_i \\ B is an open disk, simply connected. Its product collar
can be used in a van Kampen cover, once the geometrically supported
wild satellites and complement-piece homotopy equivalences have been
supplied. This script certifies geometric inequalities and cross
sections; it does NOT supply those topological equivalences.
"""
from fractions import Fraction as F
from itertools import product

eps=F(1,4); radius=F(4); dist=F(9)
t_min=F(1,2);t_max=F(17,2)
centres=((F(9),F(0),F(0)),(F(0),F(9),F(0)),(F(0),F(0),F(9)))
rotate=lambda xyz:(xyz[2],xyz[0],xyz[1])
assert tuple(map(rotate,centres))==centres[1:]+centres[:1]
assert rotate(rotate(rotate((1,2,3))))==(1,2,3)

# Each S_i misses the CENTRAL unit reference ball, its two other
# satellite reference balls, and both off-axis connector tubes.
assert dist>radius+1
assert F(162)>(radius+1)**2
assert dist-eps>radius
assert F(162)>(2*radius)**2

# Sphere-cylinder equation: (t-9)^2+u^2+v^2=16.
# For u^2+v^2<=1/16, the near graph has t>=5 and
# t<=9-sqrt(255)/4 < 8.5; far graph t>9>8.5.
assert radius**2-eps**2==F(255,16)
assert F(255,16)>(dist-t_max)**2
assert F(255,16)<radius**2
assert t_min<dist-radius<t_max<dist
# At the radial cylinder rim transversality is guaranteed by
# nonzero axial partial derivative 2(t-9) <0 on near graph.
assert dist-t_max>0
# A uniform disjoint collar of ambient spheres may be chosen.
delta=F(1,4)
assert F(162)>(2*(radius+delta))**2
assert dist>(radius+delta)+1
assert dist-eps>radius+delta
samples=0
for i,j in product(range(-8,9),repeat=2):
    u,v=F(i,32),F(j,32)
    r2=u*u+v*v
    if r2<=eps**2:
        radicand=radius**2-r2
        assert F(255,16)<=radicand<=16
        assert (dist-t_max)**2<radicand<(dist-t_min)**2
        samples+=1

print("PASS: three C3-related radius-4 separating spheres intersect each spoke in EXACTLY one disk")
print("PASS: cylinder/sphere rim transverse; disjoint radius-1/4 sphere collars")
print("PASS:",samples,"rational cross-sections; global inequality uses monotone square root")
print("CONDITIONAL VAN KAMPEN: S^2 minus closed disk is open disk => simply connected")
print("REMAINS: supported Hatcher tame cap, actual attachment to THAT wild B3, side-piece comparison")
