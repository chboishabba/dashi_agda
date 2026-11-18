#!/usr/bin/env python3
"""Exact symbolic P1/P4 discriminator for the KK/dipole/Hopf research roadmap.

CLASSICAL SOURCES:
 - Static magnetic dipole formula: standard Maxwell magnetostatics.
 - G. H. Derrick, J. Math. Phys. 5 (1964), 1252-1254,\n   DOI:10.1063/1.1704233:
   original static-scalar scaling obstruction, not this script's novelty.
 - T. H. R. Skyrme: quartic derivative stabilization, historical mechanism.
DASHI NEW: this paired exact symbolic check and explicit scope boundary.
MOTIVATION: user asked whether an imposed flux forces spiral wrapping around a
dipole and whether Derrick/Skyrme supplies a stable radius for the candidate.
This is an algebraic fixture only, not a 5D field solution or a stable soliton.
"""
import sympy as s

x, y, z, m, B0 = s.symbols("x y z m B0", real=True)
r2 = x*x + y*y + z*z
# Work in the fraction field away from r2=0.
r = s.sqrt(r2)
# Overall physical prefactor mu0/(4*pi) absorbed into m.
Bdip = s.Matrix([3*m*z*x/r**5, 3*m*z*y/r**5,
                  m*(3*z*z/r**5 - 1/r**3)])
Btotal = Bdip + s.Matrix([0, 0, B0])
# e_phi=(-y/rho,x/rho,0): its unnormalised projection is enough
# (rho = sqrt(x²+y²) != 0).
azimuth_numerator = s.factor(-y*Btotal[0] + x*Btotal[1])
assert azimuth_numerator == 0

# Axisymmetric field may still possess nulls and separatrices;
# azimuthal component=0 is NOT an absence of field curvature.
curl_components = []
for first, second, coord1, coord2 in [
    (2, 1, y, z), (0, 2, z, x), (1, 0, x, y)
]:
    curl_components.append(s.simplify(s.diff(Btotal[first],coord1) -
                                       s.diff(Btotal[second],coord2)))
assert all(v == 0 for v in curl_components), curl_components

# A Skyrme-like TWO-term scale ansatz, not original 5D Einstein dynamics.
a, b, R = s.symbols("a b R", positive=True)
E = a*R + b/R
Rstar = s.sqrt(b/a)
assert s.simplify(s.diff(E,R).subs(R,Rstar)) == 0
assert s.simplify(s.diff(E,R,2).subs(R,Rstar)) == 2*b/Rstar**3
assert s.simplify(E.subs(R,Rstar) - 2*s.sqrt(a*b)) == 0
assert s.simplify(E - 2*s.sqrt(a*b) -
    (s.sqrt(a*R) - s.sqrt(b/R))**2) == 0
print("PASS: collinear static dipole + uniform field has exactly B_phi=0")
print("PASS: exterior field curl is zero away from the singular source")
print("PASS: two-term positive-scale energy has nonnegative square defect")
print("PASS: stationary radius and positive radial second derivative")
print("NOT TESTED: original KK action, nonradial Hessian, quantum spin, gravity")
