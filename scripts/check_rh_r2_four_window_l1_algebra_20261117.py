#!/usr/bin/env python3
"""R2: exact algebra for original four-center smooth window. No R2 closure."""
import sympy as s
R,B0=s.symbols("R B0",positive=True)
lam,mu=s.symbols("lam mu",real=True)
B=s.symbols("B1:5",nonnegative=True)
A=2+s.Abs(lam)+s.Abs(mu)
assert s.simplify(sum(map(s.Abs,[s.S.One,-s.S.One,lam,mu]))-A)==0
for j in range(5):
    Bj=B0 if j==0 else B[j-1]
    from_sym_bumps=s.simplify(2*R**(1-j)*Bj*A/(2*R*B0))
    assert s.simplify(from_sym_bumps-A*Bj/(B0*R**j))==0
    print("raw L1 derivative norm upper bound j=",j,":",from_sym_bumps)
x,n,t=s.symbols("x n t",positive=True)
f=(1+t+x)**2/(1+x)**4
I=1/(n+1)+t/(n+1)**2+t*t/(3*(n+1)**3)
assert s.simplify(s.diff(I,n)+f.subs(x,n))==0
assert s.simplify(s.diff(f,x)+2*(1+t+x)*(1+2*t+x)/(1+x)**5)==0
assert s.limit(I,n,s.oo)==0
print("PASS: exact algebra, four-window normalization and fixed-t tail primitive")
print("OPEN: actual selected R/mu, unit bump derivative constants, transformed projective profile and strict signed R2 gap")
