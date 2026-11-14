#!/usr/bin/env python3
"""Exact synthetic nuisance-nullspace and covariance identity."""
import sympy as s
K=s.Matrix([[1,1],[1,-1],[1,0]])
w=s.Matrix([1,1,-2])
signal=s.Matrix([1,-1,2])
assert w.T*K == s.zeros(1,2)
S=(w.T*signal)[0]
assert S == -4
mu,n1,n2=s.symbols("mu n1 n2")
eps=s.Matrix(s.symbols("e0:3"))
residual=mu*signal+K*s.Matrix([n1,n2])+eps
assert s.expand((w.T*residual)[0]-mu*S-(w.T*eps)[0])==0
cov=s.diag(s.Rational(1,2),s.Rational(1,3),s.Rational(1,4))
assert (w.T*cov*w)[0] == s.Rational(11,6)
print("PASS exact nuisance cancellation, nonzero signal and propagated covariance")
print("WARNING: all sensitivity coefficients here are synthetic")
