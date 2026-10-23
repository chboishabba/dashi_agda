#!/usr/bin/env python3
"""First order in physical J: coordinate-time Hamiltonian and circular nodal drift.
Exact in static boosted Kerr Einstein-frame quotient; first order in spin.
Not an Earth matter solution, an eccentric orbit fit, or LARES-2 data validation.
"""
import sympy as s
import math
r,M,q,J=s.symbols('r M q J',positive=True,real=True)
F=1-2*M/r; H=1+2*M*q/r
A=F/s.sqrt(H); B=s.sqrt(H)/F; C=r*r*s.sqrt(H)
W=2*J/(r**3*H)
gtt=-A; gtp=-2*J/(r*s.sqrt(H)); gpp=C
assert s.simplify(W+gtp/gpp)==0
# t-Hamiltonian = sqrt(A*(1+p_r**2/B+L**2/C)) + W*Lz + O(J**2).
# Node is conjugate to Lz when holding total L and radial action fixed.
Oc2=s.factor(s.diff(A,r)/s.diff(C,r))
assert s.simplify(Oc2-(-s.diff(gtt,r)/s.diff(gpp,r)))==0
assert s.simplify(Oc2.subs(q,0)-M/r**3)==0
L2=s.factor(C**2*s.diff(A,r)/(A*s.diff(C,r)-C*s.diff(A,r)))
E2=s.factor(A**2*s.diff(C,r)/(A*s.diff(C,r)-C*s.diff(A,r)))
assert s.simplify(L2.subs(q,0)-M*r**2/(r-3*M))==0
assert s.simplify(E2.subs(q,0)-(r-2*M)**2/(r*(r-3*M)))==0
mu=3.986004418e14/299792458.**2
for km in (7820,12270):
    for alpha in (0.,.3,1.):
        qq=math.sinh(alpha)**2
        rr=km*1000.
        ratio=float((W/(2*J/r**3)).subs({M:mu,q:qq,r:rr}))
        assert abs(ratio-1/(1+2*mu*qq/rr))<1e-14
        assert float(Oc2.subs({M:mu,q:qq,r:rr}))>0
        print(f"r={km} km alpha={alpha}, nodal circular ratio={ratio:.15f}, delta={ratio-1:+.6e}")
print("PASS circular first-order-in-spin nodal Hamiltonian test")
print("No empirical KK/Earth inference; eccentric drift requires static radial time averaging")
