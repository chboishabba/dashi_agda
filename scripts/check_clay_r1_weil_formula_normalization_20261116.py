#!/usr/bin/env python3
"""RH R1 exact normalization/term firewall, NOT a proof of analytic Weil formula."""
from fractions import Fraction
from math import isclose, pi
from sympy import Symbol, exp, sqrt, integrate, oo, I, simplify, pi as spi
r,u,t=Symbol("r", real=True),Symbol("u", real=True),Symbol("t",positive=True)
# Gaussian is an auxiliary Fourier normalization check, NOT compactly supported
# and NOT the source of the theorem for all Weil tests.
h=exp(-t*r*r)
g=simplify(integrate(h*exp(-I*u*r),(r,-oo,oo))/(2*spi))
assert simplify(g-sqrt(spi/t)*exp(-u*u/(4*t))/(2*spi))==0
assert simplify(h.subs(r,I/2)+h.subs(r,-I/2)-2*exp(t/4))==0
assert simplify(g.subs(u,0)-1/(2*sqrt(spi*t)))==0
# von Mangoldt prime powers: 1=0, p^k=log(p), composite non-prime powers=0
def is_prime(n):
 return n>=2 and all(n%d for d in range(2,int(n**.5)+1))
def prime_power_base(n):
 for p in range(2,n+1):
  if not is_prime(p):continue
  v=n
  while v%p==0:v//=p
  if v==1:return p
 return None
assert [prime_power_base(n) for n in (1,2,4,6,8,9,10,16,27,36)]==[None,2,2,None,2,3,None,2,3,None]
# A compactly supported g yields finitely many prime-power terms:
# g(log n)=0 when n>exp(R). This is a support implication,
# not a truncation of the arithmetic side.
assert len([n for n in range(2,101) if prime_power_base(n) and n<=16])==10
print("PASS exact Fourier normalization and two symmetric pole terms")
print("PASS exact von Mangoldt prime-power classification controls")
print("CLASSICAL EXTERNAL THEOREM: completed zeta and Guinand-Weil explicit formula")
print("FIREWALL no RH, no positivity, no native Agda/Lean acceptance")
