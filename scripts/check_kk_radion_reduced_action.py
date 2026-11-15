#!/usr/bin/env python3
"""KK radion reduced-action Euler-Lagrange identity, symbolic (Jordan frame).
5D metric ds5^2=g4+phi^2(dy+k A)^2; fields independent of y.
Up to a total divergence, L4=sqrt(-g4)*(phi R4-k^2 phi^3 F2/4).
This tests the scalar variation only; not a proof of the general 5D Ricci identity.
"""
import sympy as s
phi,R4,F2,k=s.symbols("phi R4 F2 k",real=True)
L=phi*R4-k**2*phi**3*F2/4
radion=s.factor(s.diff(L,phi))
assert s.simplify(radion-(R4-s.Rational(3,4)*k**2*phi**2*F2))==0
# Trace of the reduced metric equation for constant phi:
# phi Gmunu = phi^3 k²/2 [Fmu_rho Fnu^rho - 1/4 gmunu F2]
# hence its trace is zero and R4=0.
constant_phi_trace_R4=s.Integer(0)
onshell=s.factor(radion.subs(R4,constant_phi_trace_R4))
assert s.factor(onshell)==-s.Rational(3,4)*k**2*phi**2*F2
# nonzero magnetic field => F²>0 and violates constant-radius vacuum.
b=s.symbols("b",real=True,nonzero=True)
assert s.simplify(onshell.subs({F2:2*b**2,k:1,phi:1})+s.Rational(3,2)*b**2)==0
# Yet nonzero null Maxwell F²=0 does not violate this scalar equation.
assert s.simplify(onshell.subs(F2,0))==0
print("PASS radion EL: R4 - 3*k^2*phi^2*F2/4 = 0 (Jordan scalar)")
print("PASS constant-phi metric trace R4=0 => F2=0; excludes pure magnetic fixture")
print("PASS null electromagnetic fields F2=0 are not excluded by this constraint")
print("LIMIT input KK curvature reduction identity assumed, not proved here")
