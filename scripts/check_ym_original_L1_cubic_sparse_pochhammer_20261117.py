#!/usr/bin/env python3
"""Exact original periodic L=1 SU(2) Wilson cubic coefficient.

Four independent unit-quaternion links, six commutator plaquettes.
Use the literal original Wilson deficit D=2 sum_{a<b}|Im U_a x Im U_b|².
Integrate each sparse rational monomial using all-degree S³ Pochhammer
moments, not the degree-5 24-cell (which aliases cubic terms).
Mathematical provenance: Wilson, Balaban, Pizzetti/Folland, original
DASHI rational 4D six-plane and SU2 quaternion owners.
Not an Agda-kernel proof, continuum result, or arbitrary-beta solver.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
from math import factorial
import sympy as S

N=12
ZERO=(0,)*N

def mul(A,B):
    out={}
    for aa,ca in A.items():
        for bb,cb in B.items():
            e=tuple(x+y for x,y in zip(aa,bb))
            out[e]=out.get(e,0)+ca*cb
    return {e:c for e,c in out.items() if c}

def add(A,B):
    out=A.copy()
    for e,c in B.items():out[e]=out.get(e,0)+c
    return {e:c for e,c in out.items() if c}

def scale(A,c):return {e:c*v for e,v in A.items() if c*v}

def variable(g,i):
    e=list(ZERO);e[3*g+i]=1
    return {tuple(e):1}

D={}
for a,b in combinations(range(4),2):
    for i,j in combinations(range(3),2):
        wedge=add(mul(variable(a,i),variable(b,j)),
                  scale(mul(variable(a,j),variable(b,i)),-1))
        D=add(D,scale(mul(wedge,wedge),2))
assert len(D)==54

@lru_cache(None)
def odd_double_factorial(a):
    out=1
    for j in range(a):out*=2*j+1
    return out

@lru_cache(None)
def monomial_moment(e):
    if any(n%2 for n in e):return F(0)
    v=F(1)
    for g in range(4):
        ex=e[3*g:3*g+3]
        a=sum(ex)//2
        num=1
        for z in ex:num*=odd_double_factorial(z//2)
        v*=F(num,2**a*factorial(a+1))
    return v

def integrate(poly):
    return sum((c*monomial_moment(e) for e,c in poly.items()),F(0))

# Independent symbolic quaternion identity, not merely a chosen deficit.
q=S.symbols('a b c d',real=True)
r=S.symbols('e f g h',real=True)
def quatmul(q,r):
    a,b,c,d=q;e,f,g,h=r
    return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def conj(q):return (q[0],-q[1],-q[2],-q[3])
raw=quatmul(quatmul(quatmul(q,r),conj(q)),conj(r))[0]
cross=sum((q[i]*r[j]-q[j]*r[i])**2
          for i,j in ((1,2),(1,3),(2,3)))
assert S.expand(raw-sum(v*v for v in q)*sum(v*v for v in r)+2*cross)==0

P={ZERO:1}
expected=(F(1),F(9,2),F(187,8),F(6445,48))
for k in range(4):
    observed=integrate(P)
    assert observed==expected[k],(k,observed,expected[k])
    print(f"k={k} sparse_monomials={len(P)} exact_moment={observed}")
    if k<3:P=mul(P,D)

beta=F(1,96)
lo=1-beta*expected[1]+beta**2*expected[2]/2-beta**3*expected[3]/6
hi=1-beta*expected[1]+beta**2*expected[2]/2
assert lo==F(243176723,254803968)
assert hi==F(140731,147456)
assert hi-lo==F(6445,254803968)
print(f"L1 at beta=1/96, T3<=Z<=T2: [{lo}, {hi}] width={hi-lo}")
print("ORIGINAL_L1_CUBIC_SPARSE_PIZETTI_PASS=8")
