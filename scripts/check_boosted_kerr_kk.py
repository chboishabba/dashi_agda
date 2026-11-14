#!/usr/bin/env python3
"""Sympy-checked boosted Kerr black-string Kaluza-Klein Einstein-frame quotient.
Exact 5D vacuum follows from coordinate boost of Kerr x flat line (local quotient).
No Earth interior, physical charged Earth, satellite orbit fit, or empirical bound.
"""
import math
import sympy as s
M,a,r,z,q=s.symbols("M a r z q",positive=True,real=True)
c=s.sqrt(1+q)
f=2*M*r/(r*r+a*a*z*z)
B=-2*M*a*r*(1-z*z)/(r*r+a*a*z*z)
H=1+q*f
GTphi=B*c
GTw=f*s.sqrt(q)*c
Gphiw=B*s.sqrt(q)
GTT=-1+(1+q)*f
gE_Tphi=s.simplify(s.sqrt(H)*(GTphi-GTw*Gphiw/H))
gE_TT=s.simplify(s.sqrt(H)*(GTT-GTw**2/H))
assert s.simplify(gE_Tphi-B*c/s.sqrt(H))==0
assert s.simplify(gE_TT-(-1+f)/s.sqrt(H))==0
x=s.symbols("x",positive=True)
spin=s.series(gE_Tphi.subs(r,1/x),x,0,4).removeO().expand()
tt=s.series(gE_TT.subs(r,1/x),x,0,3).removeO().expand()
assert s.simplify(spin.coeff(x,1)+2*M*a*c*(1-z*z))==0
assert s.simplify(spin.coeff(x,2)-2*M**2*a*q*c*(1-z*z))==0
assert s.simplify(tt.coeff(x,1)-M*(2+q))==0
print("PASS exact reduced Einstein-frame g_Tphi and g_TT")
print("PASS asymptotic M4=M(1+q/2), J4=Ma sqrt(1+q)")
print("At fixed J4 leading Kerr/GR frame dragging remains unchanged")
for alpha in (0., .3, 1.):
    qv=math.sinh(alpha)**2
    for km in (7820,12270):
        mm=3.986004418e14/299792458.**2
        v=float((1/s.sqrt(H)).subs({q:qv,M:mm,a:0,z:0,r:km*1000}))
        print(f"alpha={alpha}, r={km} km: metric ratio {v:.15f}, delta={v-1:+.3e}")
print("WARNING metric component ratio is not full nodal precession; no Earth KK solution")
