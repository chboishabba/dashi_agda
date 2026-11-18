#!/usr/bin/env python3
"""Single-centre KK monopole: exact Gibbons-Hawking / Taub-NUT source check.

CLASSICAL PRIOR ART:
  Gibbons & Hawking, gravitational multi-instantons (1978);
  Gross & Perry, Magnetic Monopoles in Kaluza-Klein Theories (1983);
  Sorkin, Kaluza-Klein Monopole (1983).
DASHI REUSE: SU2Bracket369OrientationBridgeExact and
BalabanCMP109SpatialC3ActionExact provide independent original YM/C3
gauge/symmetry owners. No assertion that their YM field is the KK field.
THIS ROUND: exact radial harmonic / curvature / regular-nut / first-Chern
checks for the *specific* classical metric, not a new Ricci tensor proof.
USER MOTIVATION: KK/Hopf particle, 369 YM symmetry, spin-half.
"""
import sympy as s

r, m, th, phi, rho = s.symbols("r m theta phi rho", positive=True, real=True)
V = 1 + m/r
Aphi = m*s.cos(th)
# Euclidean R3 Hodge star: *(dr)=r² sin(theta) dtheta ^ dphi.
assert s.simplify(s.diff(r*r*s.diff(V,r),r)) == 0
assert s.simplify(s.diff(Aphi,th) -
                  r*r*s.sin(th)*s.diff(V,r)) == 0
# dpsi has 4*pi*m period, hence chi=psi/m has period 4*pi.
# Its normalized 2*pi U(1) angular connection is
# a=1/2(dchi + cos(theta)dphi), with c1=-1 on oriented S2.
F_normalized = -s.sin(th)/2
chern = s.simplify(s.integrate(s.integrate(F_normalized,
                                          (th,0,s.pi)),
                              (phi,0,2*s.pi))/(2*s.pi))
assert chern == -1
# As r->0, rho=2*sqrt(m*r). With chi=psi/m, the 4D metric
# becomes drho² + rho²/4 [dtheta²+sin²theta dphi²+
# (dchi+cos(theta)dphi)²], the flat R4 polar metric, if
# period(chi)=4*pi. A local check is NOT geodesic completeness.
near = rho**2/(4*m)
assert s.limit(V.subs(r,near)*s.diff(near,rho)**2,rho,0) == 1
assert s.limit((V*r*r).subs(r,near)/rho**2,rho,0) == s.Rational(1,4)
assert s.limit((m*m/V).subs(r,near)/rho**2,rho,0) == s.Rational(1,4)
# The exterior U(1) curvature is rotationally covariant. For a
# literal xyz cycle, P(x,y,z)=(z,x,y), the monopole Cartesian field
# B=-m(x,y,z)/r³ transforms exactly under the SAME cyclic action.
x,y,z = s.symbols("x y z", real=True)
norm = s.sqrt(x*x+y*y+z*z)
B = s.Matrix([-m*x/norm**3,-m*y/norm**3,-m*z/norm**3])
P = s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
rotated = s.Matrix([v.subs({x:z,y:x,z:y}, simultaneous=True) for v in B])
assert all(s.simplify(a-b)==0 for a,b in zip(rotated, P*B))
assert P**3 == s.eye(3)
# String-free north/south potentials, nonzero transition.
a_north = (s.cos(th)-1)/2
a_south = (s.cos(th)+1)/2
assert s.simplify(s.diff(a_north,th)-F_normalized)==0
assert s.simplify(s.diff(a_south,th)-F_normalized)==0
assert s.simplify(a_south-a_north)==1
print("PASS KK single-centre: harmonic V and dA=*dV")
print("PASS normalized c1=-1 and north/south patch transition")
print("PASS smooth-nut local radial/angle asymptotics with chi period 4pi")
print("PASS physical spatial xyz C3 covariance of monopole curvature")
print("OPEN full R_AB=0 independent tensor calculation, global mass/energy")
print("OPEN particle configuration space and FR rotation/exchange loops")
print("OPEN SU2 YM field-to-KK U1 connection same-object identification")
