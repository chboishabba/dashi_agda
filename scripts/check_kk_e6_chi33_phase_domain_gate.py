#!/usr/bin/env python3
"""Domain gate for phase-only Chi33 boundary Wess-Zumino compensation.

Original anomaly context: Scrucca et al. (2002); von Gersdorff and Quiros
(2003). Existing chosen first-Tits 27 source: dashi_agda #1106; selected
CS/Chi33 phase anomaly cancellation ansatz: dashi_agda #1241.
New necessary *field-space* acceptance test: Johl Brown / ChatGPT-assisted
source-written reasoning. Not a global gauge anomaly theorem.

A phase-only WZ functional exp(i n arg(z)) is continuous on C\{0},
but cannot extend continuously to zero unless n=0, since limits from
r>0 along different rays disagree. Couplings to topological charges
replace n by their charge-dependent integers; a nonzero sector is enough
to obstruct the universal phase-only extension to the entire scalar
configuration space. This does not exclude constrained |z|>0 sectors,
patchwise differential cocycles, UV fermions, or another counterterm.
"""
import cmath
from fractions import Fraction
from math import pi

def phase_from_ray(n, angle):
    return cmath.exp(1j*n*angle)

for n in (-4,-3,-2,-1,1,2,3,4):
    # two rays, same limiting zero, distinct limiting functional values.
    left=phase_from_ray(n,0)
    right=phase_from_ray(n,pi/abs(n))
    assert abs(left-1)<1e-12
    assert abs(right+1)<1e-12
    # Evaluated at arbitrarily small radii the result is unchanged.
    for radius in (1, Fraction(1,10**6),Fraction(1,10**12)):
        z0=complex(float(radius),0)
        z1=float(radius)*cmath.exp(1j*pi/abs(n))
        assert abs(phase_from_ray(n,cmath.phase(z0))-1)<1e-12
        assert abs(phase_from_ray(n,cmath.phase(z1))+1)<1e-12
assert all(abs(phase_from_ray(0,theta)-1)<1e-12
           for theta in (0,pi/7, pi, 2*pi))
print("PASS phase-only WZ nonzero winding cannot extend continuously to Chi33=0")
print("PASS zero topological coefficient does extend: sector-specific obstruction")
print("OPEN source action may restrict |Chi33|>0, use patches/defects or UV fermion completion")
print("OPEN quotient-bundle global phase and regulator remain independent gates")
