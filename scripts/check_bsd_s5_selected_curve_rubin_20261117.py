#!/usr/bin/env python3
"""BSD S5 original E exact scalar algebra, with classical Rubin theorem as premise.

This does NOT computationally prove Rubin's CM theorem, the exact period/L
identity, Galois Selmer cohomology, or native Agda/Lean kernel acceptance.
"""
import sympy as sp
L, Omega, Sha = sp.symbols("L Omega Sha", positive=True)
reg, c2, tors = sp.Integer(1), sp.Integer(2), sp.Integer(4)
assert reg*c2/tors**2 == sp.Rational(1,8)
assert sp.solve(sp.Eq(L,Omega*reg*c2*Sha/tors**2).subs(Omega,8*L),Sha)==[1]
assert sp.simplify((Omega*reg*c2/tors**2).subs(Omega,8*L)-L)==0
assert 4**2==16 and 2*8==16
print("PASS: selected E:y^2=x^3-x strong BSD scalar with Omega=8L, c2=2, tors=4, rank=0, Sha=1")
print("External imported inputs: Rubin CM odd-primary BSD and finiteness, S3 Sha[2]=0, S4 nonzero L and exact period normalization")
print("No native Lean/Agda acceptance; no universal BSD")
