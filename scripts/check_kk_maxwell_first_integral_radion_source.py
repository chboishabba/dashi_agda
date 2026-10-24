#!/usr/bin/env python3
"""KK magnetic sector: exact first-integral solution and stress consistency.
Jordan-frame reduced action is assumed. Flat-base reduction is a diagnostic,
not a claim the full Einstein equations hold.
"""
import sympy as s
x,k,Q=s.symbols("x k Q",real=True,nonzero=True)
phi=s.Function("phi")(x)
aprime=Q/phi**3
maxwell=s.factor(s.diff(phi**3*aprime,x))
assert maxwell==0
F2=s.factor(2*aprime**2)
radion=s.factor(3*k**2*phi**2*F2/4)
assert s.simplify(radion-3*k**2*Q**2/(2*phi**4))==0
# If the metric were flat then R4=0, so the radion equation requires Q=0.
# This is a no-go for that *particular* flat metric, not for curved spacetime.
print("PASS Maxwell first integral: phi^3 * A_y' = Q")
print("PASS F2 = 2*Q^2/phi^6")
print("PASS radion source term = 3*k^2*Q^2/(2*phi^4)")
print("FLAT METRIC NO-GO: R4=0 fails nonzero-Q radion equation")
print("REMAINING: solve coupled nonflat 4D Einstein/radion equations")
