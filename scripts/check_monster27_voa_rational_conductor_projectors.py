#!/usr/bin/env python3
"""Exact rational Monster Vnatural2 C27 conductor projectors.

Q_d=(1/27) sum_(j=0)^26 c_d(j)*rho(g)^j with Ramanujan sums.
External premises: FLM rational weight-two Monster group action and
ATLAS/McKay-Thompson trace 1,27A/B,9B,3B values 196884,3,0,54.
These are polynomial endomorphisms of that ACTUAL action. This script
checks identities in Q[C27] and F127[C27], NOT an actual 196884 matrix.
"""
from fractions import Fraction
from math import gcd
from itertools import product
import sympy as s
N=27;D=(1,3,9,27)
traces={j:(196884 if j==0 else 54 if j%9==0 else 0 if j%3==0 else 3)
        for j in range(N)}
def phi(n):return sum(gcd(k,n)==1 for k in range(n))
def ram(d,j):
 h=gcd(d,j)
 return int(s.mobius(d//h)*phi(d)//phi(d//h))
Q={d:tuple(Fraction(ram(d,j),N) for j in range(N)) for d in D}
def mul(A,B):
 out=[Fraction(0)]*N
 for i,a in enumerate(A):
  for j,b in enumerate(B):out[(i+j)%N]+=a*b
 return tuple(out)
zero=(Fraction(0),)*N
identity=(Fraction(1),)+(Fraction(0),)*(N-1)
for a,b in product(D,repeat=2):
 assert mul(Q[a],Q[b])==(Q[a] if a==b else zero)
assert tuple(sum(Q[d][j] for d in D) for j in range(N))==identity
ranks={d:sum(Q[d][j]*traces[j] for j in range(N)) for d in D}
assert ranks=={1:7298,3:14590,9:43776,27:131220}
assert sum(ranks.values())==196884
p=127
inv=pow(27,-1,p)
Qp={d:tuple(ram(d,j)*inv%p for j in range(N)) for d in D}
def mulp(A,B):
 out=[0]*N
 for i,a in enumerate(A):
  for j,b in enumerate(B):out[(i+j)%N]=(out[(i+j)%N]+a*b)%p
 return tuple(out)
z=(0,)*N;identityp=(1,)+(0,)*(N-1)
for a,b in product(D,repeat=2):
 assert mulp(Qp[a],Qp[b])==(Qp[a] if a==b else z)
assert tuple(sum(Qp[d][j] for d in D)%p for j in range(N))==identityp
assert (p-1)%27!=0
print("PASS exact Q[C27] and F127[C27] projector identities")
print("PASS source-derived rational eigenspace dimensions",ranks)
print("NEXT use mmgroup rho127 with a CERTIFIED order27 Monster word")
print("OPEN actual VOA Griess u_1 v for noncentral cube bonds")
