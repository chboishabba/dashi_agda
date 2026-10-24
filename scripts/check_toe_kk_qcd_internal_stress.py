#!/usr/bin/env python3
"""Same 5D EFT: Casimir radion potential -> fifth-direction stress.

At physical Jordan circle length L=2*pi*b, the renormalized 4D
vacuum energy V_J(b) is the energy per noncompact 3-volume.
The 5D pressure conjugate to L is p5=-dV_J/dL.
A 4D Einstein-frame U(x)=ell/x+W(x)/x**6 satisfies
V_J=(b/b0)**2*V_E. For 4D flat tuning V_E(1)=0,
p5 = -[c0/(2*pi*b0**5)]*(W'(1)-5W(1)).
Hence QCD stationarity obstruction is also an INTERNAL STRESS
residual. This is an effective-action stress identity, NOT a proof
of an exact nonlinear quantum-corrected 5D Earth solution.

Scientific prior: classical KK 5D Einstein source and Casimir
variation / Brown-Maclay stress; repo #1165 source-native stress.
"""
import sympy as s
from mpmath import mp
x,b0,c0,ell=s.symbols("x b0 c0 ell",positive=True,real=True)
W=s.Function("W")
U=ell/x+W(x)/x**6
VE=c0/b0**4*U
VJ=s.factor(x*x*VE)
rho5=s.simplify(VJ/(2*s.pi*b0*x))
p5=s.simplify(-s.diff(VJ,x)/(2*s.pi*b0))
W0,Wprime=s.symbols("W0 Wprime",real=True)
sub={ell:-W0,W(1):W0,s.Subs(s.Derivative(W(x),x),x,1):Wprime}
rho=s.simplify(rho5.subs(x,1).subs(sub))
pressure=s.simplify(p5.subs(x,1).subs(sub))
D=Wprime-5*W0
assert rho==0
assert s.simplify(pressure+c0*D/(2*s.pi*b0**5))==0
assert s.simplify((s.diff(U,x).subs(x,1).subs(sub))-D)==0
# Strict constant-circle product Einstein compatibility:
# T55=1/2 Tr(T4). Vacuum 4D stress is -rho5 g_4; trace=-4rho5,
# so p5=-2rho5, and for flat vacuum rho5=0 -> p5=0.
residual=s.simplify(pressure+2*rho)
assert s.simplify(residual + c0*D/(2*s.pi*b0**5))==0
# QED-only tuned D=0: both 5D vacuum stresses vanish.
assert pressure.subs(Wprime,5*W0)==0
# Physical QED+QCD, retuning Lambda to keep V_E=0,
# leaves D~ -240 -> positive inward-direction pressure.
mp.dps=40
physicalD=mp.mpf('-239.99999999978987694')
coef=3*mp.zeta(5)/(64*mp.pi**6)
HBARC=mp.mpf('0.1973269804e-15')
b_gev=mp.mpf('1e-24')/HBARC
p5_gev5=-coef*physicalD/(2*mp.pi*b_gev**5)
assert p5_gev5>0
print("EXACT VJ(x)=x^2 VE(x), rho5=VJ/(2pi*b), p5=-dVJ/d(2pi*b)")
print("EXACT after Minkowski energy retuning: rho5=0, p5=-(c0/2pi b0^5)*(W'-5W)")
print("EXACT 5D Ricci-flat product stress condition p5=Tr(T4)/2=-2rho5")
print("NUMERIC D_QCD=",mp.nstr(physicalD,20),
      "p5 residual GeV^5=",mp.nstr(p5_gev5,12))
print("PASS bulk cosmological retune cannot simultaneously cancel 4D vacuum energy and 5D pressure in this field spectrum")
print("BOUNDARY one-loop effective stress; source equations/backreaction/exact-head Agda remain open")
