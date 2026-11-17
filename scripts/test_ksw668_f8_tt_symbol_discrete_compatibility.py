#!/usr/bin/env python3
"""Exact original F8 TT Fourier-symbol/divergence compatibility audit.

KSW668 original tensor-source attribution retained. Algebra is necessary
for a mimetic discrete TT tensor, not proof of original radial-FV TT parity.
"""
import sympy as s

a,b,c=s.symbols("a b c")
k=s.Matrix([a,b,c])
K=k.dot(k)
P=K*s.eye(3)-k*k.T
Q=s.diag(0,1,-1)
T=s.expand(P*Q*P-s.Rational(1,2)*P*s.trace(P*Q))
checks={
  "projector_null":(P*k).applyfunc(s.expand)==s.zeros(3,1),
  "projector_square":(P*P-K*P).applyfunc(s.expand)==s.zeros(3,3),
  "tt_divergence":(T*k).applyfunc(s.expand)==s.zeros(3,1),
  "tt_trace":s.expand(s.trace(T))==0,
  "tt_symmetric":T==T.T,
}
t0=T.subs({a:1,b:2,c:3})
checks["same_symbol_example"]=(t0*s.Matrix([1,2,3])==s.zeros(3,1))
mismatch=t0*s.Matrix([1,1,2])
checks["mixed_symbol_counterexample"]=(mismatch==s.Matrix([-s.Rational(3,2),-24,s.Rational(33,2)]))
q=s.Matrix(s.symbols("u v w"))
checks["general_mixed_symbol_defect"]=(T*q-T*(q-k)).applyfunc(s.expand)==s.zeros(3,1)
print("Original projector component T(1,2,3):")
print(t0)
print("Incompatible divergence:",list(mismatch))
for name,ok in checks.items():
    print(name, "PASS" if ok else "FAIL")
assert all(checks.values())
print(f"{len(checks)}/{len(checks)} exact tensor-symbol checks passed")
