#!/usr/bin/env python3
"""R2 unconditional explicit zero shell A=160, conditional smooth-kernel C.

This checker verifies symbolic arithmetic and conservative real-inequality
reduction. It does NOT prove the cited zero-count theorem or selected-W norms.
"""
from math import comb
import sympy as s
k,t,n,x,r,L,a=s.symbols("k t n x r L a",nonnegative=True)
m=s.symbols("M0:5",nonnegative=True)
N=s.symbols("N",positive=True)
# Published Bellotti--Wong (2025): for U>=e,
# |N(U)-U/(2*pi)log(U/(2*pi*e))|
# <=0.10076 log(U)+0.24460 log log(U)+8.08344.
# Since loglog(U)<=log(U) and U log U>=e for U>=e:
# N(U) <= (1+0.34536+8.08344/e)*U log U <5 U log U.
assert 1+s.Rational(10076,100000)+s.Rational(24460,100000)+s.Rational(808344,100000)/s.E <5
# For U<e use monotonic N(U)<=N(e) <= 5e <20.
assert s.N(5*s.E)<20
# Therefore N(U) <=20(1+U)log(e+U), all U>=0.
# Every two-sided unit shell is bounded by 2 N(t+k+1), including multiplicities.
# For X=1+t+k >=2:
# 2*20*(1+t+k+1)*log(e+t+k+1)
# <=160*(1+t+k)*log(e+t+k).
X=s.symbols("X",positive=True)
assert s.expand(2*40*X-40*(X+1))==40*(X-1)
assert s.limit(s.log(s.E+X+1)/s.log(s.E+X),X,s.oo)==1
# Log inequality log(e+X+1)<=2log(e+X) for X>=1,
# since (e+X)^2 >= e+X+1. Prove polynomial difference positive:
assert s.expand((s.E+X)**2-(s.E+X+1)) == X**2+X*(2*s.E-1)+s.E**2-s.E-1
assert s.N(s.E**2-s.E-1)>0

# Fourier family F(alpha,q)=integral P(u)exp(alpha*u)exp(i*q*u)du
# supp P subset [-L,L], |alpha|<=a:
# |F| <= exp(aL) sum_j binom(4,j)a^(4-j)||P^(j)||_1 / |q|^4.
D=s.expand(sum(comb(4,j)*a**(4-j)*m[j] for j in range(5)))
assert D==m[4]+4*a*m[3]+6*a*a*m[2]+4*a**3*m[1]+a**4*m[0]
# Source physical scaling is mult/r^2 * F(alpha,(gamma-t)/r);
# k<=|gamma-t|, k>=1 => |term|/mult <=
# 16*r^2*exp(aL)*D/(k+1)^4.
C=16*r*r*D
assert s.simplify(C/(16*r*r)-D)==0

# The older tail-majorant used 4*A*C; retain its algebra.
f=(1+t+x)**2/(1+x)**4
I=s.integrate(f,(x,n,s.oo))
J=1/(n+1)+t/(n+1)**2+t*t/(3*(n+1)**3)
assert s.simplify(I-J)==0
assert s.simplify(s.diff(f,x)+2*(1+t+x)*(1+2*t+x)/(1+x)**5)==0
assert s.limit(f.subs(x,n)+I,n,s.oo)==0
print("PASS: unconditional shell constant A=160 arithmetic (using cited zero theorem)")
print("PASS: conditional fourth-derivative Fourier envelope and normalized rescaling")
print("C(t,W) = 16*(t/16)^2*exp(L*a)*(",D,")")
print("PASS: symbolic fixed-t cofinal O(1/n) bound")
print("NOT DONE: selected-W Fourier identity, explicit L and M_j, certified finite signed gap, uniform t/rho margin, native kernel")
