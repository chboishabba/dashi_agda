#!/usr/bin/env python3
"""Exact conditional fixed-t R2 far-zero shell bound (not the R2 signed gap)."""
import sympy as s
x,n,t,A,C=s.symbols('x n t A C',positive=True)
f=(1+t+x)**2/(1+x)**4
I=s.integrate(f,(x,n,s.oo))
expected=1/(n+1)+t/(n+1)**2+t*t/(3*(n+1)**3)
assert s.simplify(I-expected)==0
assert s.simplify(s.diff(f,x)+2*(t+x+1)*(2*t+x+1)/(x+1)**5)==0
bound=s.factor(4*A*C*(f.subs(x,n)+expected))
assert s.limit(bound,n,s.oo)==0
print("PASS: conditional fourth-decay zero-shell sum, integral, monotonicity, tail limit")
print("tail <=",bound)
print("OPEN: prove source-specific decay constant, compute signed compensation and strict cofinal gap")
