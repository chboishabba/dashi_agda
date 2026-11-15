#!/usr/bin/env python3
"""Exact Fourier-amplitude / detector-weight examples reusing Shor principles.
Not Shor factoring, a continuum path integral, or a calibrated NV simulation.
"""
import sympy as s
I=s.I
# Q=3 character table: exact cyclic DFT, no floating-point approximation.
omega=s.exp(2*s.pi*I/3)
F=s.Matrix(3,3,lambda k,j:omega**(k*j)/s.sqrt(3))
assert all(s.simplify(x)==0 for x in (F.conjugate().T*F-s.eye(3)))
psi=s.Matrix([1,1,1])/s.sqrt(3)
out=s.simplify(F*psi)
assert all(s.simplify(out[i]-(1 if i==0 else 0))==0 for i in range(3))
weights=[s.simplify(out[i]*s.conjugate(out[i])) for i in range(3)]
assert weights==[1,0,0] and sum(weights)==1
# Dephasing of the completely uniform pure state to a classical mixture.
rho=psi*psi.conjugate().T
dephased=s.diag(*[rho[i,i] for i in range(3)])
P0=s.diag(1,0,0)
coherent=s.simplify(s.trace(P0*F*rho*F.conjugate().T))
incoherent=s.simplify(s.trace(P0*F*dephased*F.conjugate().T))
assert coherent==1 and incoherent==s.Rational(1,3)
assert s.simplify(s.trace(rho)-1)==0
assert s.simplify(s.trace(dephased)-1)==0
print("PASS exact Q3 unitary cyclic Fourier, Born weights, trace preservation")
print("PASS coherent port P=1 versus dephased port P=1/3")
print("BOUNDARY: physical source-to-phase S/hbar and diamond optical response uncalibrated")
