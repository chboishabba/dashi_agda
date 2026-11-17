#!/usr/bin/env python3
"""Original F8 source fourth derivative vs FV endpoint primitive exact weld.

Compares exact original analytic formulas from
scripts/ksw668_f8_tt_multipole.py and
scripts/ksw668_f8_fv_source_flux.py on arbitrary smooth f(u).
This is symbolic calculus, not a kernel Agda proof or receiver convergence.
"""
import sympy as s
u=s.symbols('u',positive=True)
f=s.Function('f')(u)
d=[f]+[s.diff(f,u,n) for n in range(1,5)]
p0=s.Rational(2,5)*(u*u*d[3]+2*u*d[2]-2*d[1])
p2=s.Rational(4,7)*(u**4*d[3]-3*u**3*d[2]+3*u**2*d[1])
p4=(u**6*d[3]-12*u**5*d[2]+75*u**4*d[1]-315*u**3*f)/35
source0=s.Rational(2,5)*(u**2*d[4]+4*u*d[3])
source2=s.Rational(4,7)*(u**4*d[4]+u**3*d[3]-6*u**2*d[2]+6*u*d[1])
source4=(u**6*d[4]-6*u**5*d[3]+15*u**4*d[2]-15*u**3*d[1])/35
checks=[s.expand(s.diff(p0,u)-source0),
        s.expand(s.diff(p2,u)-source2),
        s.expand(s.diff(p4,u)+27*u**2*f-source4)]
assert all(z==0 for z in checks),checks
print('3/3 original F8 source/finite-volume primitive derivative identities PASS')
