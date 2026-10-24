#!/usr/bin/env python3
"""Jordan-matter-derived scalar source and uniform-sphere fifth-force profile.
A positive radion mass m is EXTERNAL here, not derived from the winding
model rejected by check_kk_single_action_winding_steelman.py.
"""
import sympy as s
from mpmath import mp

r,R,m,rho,Mp=s.symbols("r R m rho Mp",positive=True,real=True)
source=rho/(s.sqrt(6)*Mp)
A=-source*(R*m+1)*s.exp(-R*m)/m**3
B=source*(R*m*s.cosh(R*m)-s.sinh(R*m))/m**3
inside=source/m**2+A*s.sinh(m*r)/r
outside=B*s.exp(-m*r)/r
def helmholtz(f):
    return s.diff(f,r,2)+2*s.diff(f,r)/r-m**2*f
assert s.simplify(helmholtz(inside)+source)==0
assert s.simplify(helmholtz(outside))==0
assert s.simplify(inside.subs(r,R)-outside.subs(r,R))==0
assert s.simplify(s.diff(inside,r).subs(r,R)-s.diff(outside,r).subs(r,R))==0
assert s.limit(inside,r,0).is_finite

G=1/(8*s.pi*Mp**2)
mass=4*s.pi*rho*R**3/3
newton=-G*mass/r
scalar=-outside/(s.sqrt(6)*Mp)
z=m*R
shape=(z*s.cosh(z)-s.sinh(z))/z**3
ratio=shape*s.exp(-m*r)
assert s.simplify(scalar/newton-ratio)==0
assert s.simplify(s.diff(scalar,r)/s.diff(newton,r)-ratio*(1+m*r))==0
assert s.limit(shape,m,0)==s.Rational(1,3)
mp.dps=45
radius=mp.mpf("6371000")
orbital_radius=mp.mpf("12270000")
for zz in ("0.01","0.1","1","5","10","20"):
    t=mp.mpf(zz)
    finite_shape=(t*mp.cosh(t)-mp.sinh(t))/t**3
    strength=finite_shape*mp.exp(-t*orbital_radius/radius)*(1+t*orbital_radius/radius)
    print(f"m*R={zz:>5}: scalar/Newton force at sample orbit={float(strength):.9g}")
print("PASS fixed Jordan source coefficient, exact C1 sphere solution and Yukawa ratio")
print("NOT measured fifth force: bare-Newton normalization; Earth multipoles, physical mass source and screening missing")
