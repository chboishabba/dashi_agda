#!/usr/bin/env python3
"""Source-anchored exact C27 Fourier projectors on Vnatural weight two.

EXTERNAL premises, never attributed to this script: FLM Monster Vnatural;
ATLAS: 27A/B cube=9B and ninth=3B; Conway-Norton/Ford-McKay-Norton
q^1 ordinary UNTWiSTED graded traces = (3,0,54), dim V2=196884.
Pi_k(g)=1/27 sum_j zeta27^{-kj} rho(g)^j is a literal endomorphism
of actual Monster grade-two states once the existing VOA action is
instantiated. This script computes its rank using cyclotomic arithmetic
without making 196884x196884 matrices or fake twisted module data.
"""
from math import gcd
from collections import Counter
import sympy as s

N=27
x=s.Symbol("x")
cyclotomic=s.Poly(x**18+x**9+1,x,domain=s.QQ)
def trace(j):
    j%=N
    if j==0:return 196884
    if j%9==0:return 54
    if j%3==0:return 0
    return 3
assert Counter(trace(j) for j in range(N))=={196884:1,54:2,0:6,3:18}
def reduce(poly):
    return s.Poly(poly,x,domain=s.QQ).rem(cyclotomic).as_expr()
ranks={}
for k in range(N):
    tr_pi=reduce(sum(trace(j)*x**((-k*j)%N) for j in range(N)))
    assert tr_pi.is_Integer and int(tr_pi)%27==0
    ranks[k]=int(tr_pi)//27
expect={1:7298,3:7295,9:7296,27:7290}
assert all(ranks[k]==expect[N//gcd(k,N)] for k in range(N))
assert sum(ranks.values())==196884
for d in range(N):
    assert reduce(sum(x**((d*j)%N) for j in range(N)))==(27 if d==0 else 0)
assert [sum(ranks[k] for k in range(N) if k%3==j) for j in range(3)]==[65664,65610,65610]
print("PASS actual-source Fourier projectors: all 27 integer ranks",Counter(ranks.values()))
print("PASS exact Q(zeta27) character orthogonality")
print("PASS 3B counts (neutral,+,-)=65664,65610,65610")
print("OPEN noncentral geometric edge Griess-mode amplitudes and physical KK/AdS3 operator")
