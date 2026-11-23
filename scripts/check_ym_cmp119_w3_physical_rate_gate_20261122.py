#!/usr/bin/env python3
"""Exact 1D Ising decimation and physical-rate sanity check; NOT a Wilson SU(N) test."""
import sympy as s
a, R, J = s.symbols("a R J", positive=True)
q = s.tanh(J)
assert s.simplify(s.tanh(s.atanh(q*q))-q*q) == 0
assert s.simplify(s.diff(s.atanh(q*q), J)-2*q/(1+q*q)) == 0
assert s.simplify(s.cosh(2*J)-(1+q*q)/(1-q*q)) == 0
q1, q2 = (1-a)/(1+a), (1-a*a)/(1+a*a)
assert s.simplify((1-a)/(1+a)-q1) == 0
assert s.limit(q1**(R/a),a,0,dir="+") == s.exp(-2*R)
assert s.limit(q2**(R/a),a,0,dir="+") == 1
print("PASS: exact decimation and contrasting physical-cutoff limits (toy diagnostic)")
