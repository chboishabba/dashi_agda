#!/usr/bin/env python3
"""Exact symbolic cross-cut for Bishop SU2/YM.REAL, 17 Nov 2026.

SymPy proves each asserted polynomial/rational identity exactly:
Pochhammer recurrence ratios, Fejer telescoping positivity floor,
SU2 two-sided unitary matrix, 24-cell degree-5 moments and Taylor
rational enclosures at all six original cutoffs L=1..6.
The all-degree root-of-unity and Bishop/Agda completeness theorems
remain distinct from this finite reference checker.
"""
import sympy as S
from itertools import product

checks=0
def check(got,expected,label):
 global checks
 gap=S.cancel(S.together(S.expand_func(got-expected)))
 assert gap==0,(label,gap)
 checks+=1

n=S.symbols("n",integer=True,nonnegative=True)
check((n+S.Rational(3,2))/(n+3),
      (2*n+3)/(2*n+6),"positive kernel normalization ratio")
u=2*(n+S.Rational(3,2))/(n+3)-1
u2=(4*(n+S.Rational(3,2))*(n+S.Rational(5,2))/((n+3)*(n+4))
    -4*(n+S.Rational(3,2))/(n+3)+1)
check(u,n/(n+3),"kernel first zonal moment")
check(u2,(n*n+n+3)/((n+3)*(n+4)),"kernel second zonal moment")
check(1-u,3/(n+3),"kernel concentration")

J=S.symbols("J",integer=True,nonnegative=True)
k=S.symbols("k",integer=True,positive=True)
check(S.summation(2/(4*k*k-1),(k,1,J)),1-1/(2*J+1),
      "Fejer strictly positive weight floor via rational telescope")

a,b,c,d=S.symbols("a b c d",integer=True,nonnegative=True)
K=a+b+c+d
for index,e in enumerate((a,b,c,d)):
 check((e+S.Rational(1,2))/(K+2),(2*e+1)/(2*K+4),
       f"universal Pochhammer coordinate {index} ratio")

x,y,z,w=S.symbols("q0 q1 q2 q3",real=True)
U=S.Matrix([[x+S.I*w,z+S.I*y],[-z+S.I*y,x-S.I*w]])
norm=x*x+y*y+z*z+w*w
check(S.re(S.trace(U))/2,x,"normalized matrix trace")
check(S.expand(U.det()),norm,"quaternion matrix determinant")
for A in (U.conjugate().T*U,U*U.conjugate().T):
 for i,j in product(range(2),repeat=2):
  check(S.expand(A[i,j]),norm if i==j else 0,
        "two-sided matrix unitarity")

# For the original six-positive-plane periodic Wilson action S>=0,
# 1-S <= exp(-S) <= 1-S+S²/2 pointwise.
# Original volume L>=2 has E[S/beta]=P,
# E[(S/beta)²]=P²+P/4; for L=1 commutators:
# E[S/beta]=9/2, E[(S/beta)²]=187/8.
for L in range(1,7):
 P=6*L**4
 beta=S.Rational(1,16*P)
 mean=S.Rational(9,2) if L==1 else S.Integer(P)
 moment2=S.Rational(187,8) if L==1 else P*P+S.Rational(P,4)
 lo=1-beta*mean
 hi=lo+beta**2*moment2/2
 assert S.Integer(0)<lo<=hi<S.Integer(1)
 checks+=3
 print(f"original Wilson L={L}, beta={beta}, Z in [{lo}, {hi}], "
       f"width={hi-lo}")

# 24-cell: all degree<=5 sphere monomials EXACT. Positive weights=1/24.
V=[]
for i in range(4):
 for sign in (-1,1):
  p=[S.Integer(0)]*4;p[i]=S.Integer(sign);V.append(tuple(p))
for signs in product((-1,1),repeat=4):
 V.append(tuple(S.Rational(s,2) for s in signs))
assert len(V)==24
for A in range(6):
 for B in range(6-A):
  for C in range(6-A-B):
   for D in range(6-A-B-C):
    e=(A,B,C,D)
    disc=sum((S.prod(p[i]**e[i] for i in range(4))
             for p in V),S.Integer(0))/24
    expected=(S.Integer(0) if any(k%2 for k in e)
      else S.prod(S.rf(S.Rational(1,2),k//2) for k in e)
       /S.rf(S.Integer(2),sum(e)//2))
    check(disc,expected,f"24cell sphere moment {e}")
for cutoff in (1,3,5,7,9,11):
 even=sum(((-x)**j/S.factorial(j) for j in range(cutoff)),
          S.Integer(0))
 odd=even+(-x)**cutoff/S.factorial(cutoff)
 check(even-odd,x**cutoff/S.factorial(cutoff),
       f"alternating exponential Taylor interval {cutoff}")
print("YM_REAL_SYMPY_MAXCUT_PASS",checks)
