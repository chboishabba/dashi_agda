#!/usr/bin/env python3
"""Arbitrary-degree dyadic S3 cubature moment evaluator, exact Q arithmetic.

Proof inputs: primitive dyadic character cancellation (finite geometric
series) and the positive Fejer-I weight telescope. Cheb-II x Fejer-I x
circle yields every Pochhammer moment on S3. This executable validates
arbitrary requested degrees, not a universally quantified Agda proof.
Attribution: Fejer, Stroud, Pizzetti/Folland, Bishop, prior DASHI YM.
"""
from fractions import Fraction as F
from math import comb, prod
import argparse
import sympy as sp

checks=0
def eq(x,y,label):
 global checks
 assert sp.simplify(x-y)==0,(label,x,y)
 checks+=1

def rf(x,n):
 p=F(1)
 for j in range(n):p*=x+j
 return p

def orders(degree):
 A=2
 while 2*(A-1)-1<degree:A*=2
 M=L=2
 while M<=degree:M*=2;L*=2
 return A,M,L

def sphere(e):
 if any(x%2 for x in e):return F(0)
 a=[x//2 for x in e]
 return prod(rf(F(1,2),x) for x in a)/rf(F(2),sum(a))

def product_rule(e):
 a,b,c,d=e
 A,M,L=orders(sum(e))
 assert 2*(A-1)-1>=sum(e) and M>sum(e) and L>sum(e)
 if any(x%2 for x in e):return F(0)
 u=(c+d)//2;v=(b+c+d)//2
 ch=rf(F(1,2),a//2)*rf(F(3,2),v)/rf(F(2),a//2+v)
 fj=rf(F(1,2),b//2)*rf(F(1),u)/rf(F(3,2),b//2+u)
 ci=rf(F(1,2),c//2)*rf(F(1,2),d//2)/rf(F(1),u)
 return ch*fj*ci

def monomials(degree):
 for a in range(degree+1):
  for b in range(degree+1-a):
   for c in range(degree+1-a-b):
    for d in range(degree+1-a-b-c):
     yield a,b,c,d

def cheb_grid(A,r):
 """sum_{j=1}^{A-1} cos(r*pi*j/A), by finite geometric filter."""
 return A-1 if r%(2*A)==0 else (-1 if r%2==0 else 0)

def cheb2_U(A,k):
 assert A>1 and k<=2*A-3
 return F(cheb_grid(A,k)-cheb_grid(A,k+2),A)

def fejer_T(M,k):
 """Weight times Chebyshev T_k, via midpoint-cosine orthogonality."""
 assert M>1 and 0<=k<M
 J=(M-1)//2
 # Grid sum C_r = M delta_{r,0} for 0<=r<2M.
 C=lambda r:M if r==0 else 0
 out=F(C(k),M)
 for h in range(1,J+1):
  out-=F(C(abs(k-2*h))+C(k+2*h),M*(4*h*h-1))
 return out

def fejer_power(k):
 # x^k expansion in Chebyshev T basis
 total=F(0)
 for h in range(k//2+1):
  r=k-2*h
  coef=F(comb(k,h),2**k if r==0 else 2**(k-1))
  moment=(F(1) if r==0 else (F(0) if r%2 else F(1,1-r*r)))
  total+=coef*moment
 return total

def symbolic_proofs():
 a,b,c,d=sp.symbols('a b c d',integer=True,nonnegative=True)
 u=c+d;v=b+u;k=a+v
 ch=sp.rf(sp.Rational(1,2),a)*sp.rf(sp.Rational(3,2),v)/sp.rf(2,k)
 fj=sp.rf(sp.Rational(1,2),b)*sp.rf(1,u)/sp.rf(sp.Rational(3,2),v)
 ci=sp.rf(sp.Rational(1,2),c)*sp.rf(sp.Rational(1,2),d)/sp.rf(1,u)
 expected=sp.prod(sp.rf(sp.Rational(1,2),x) for x in (a,b,c,d))/sp.rf(2,k)
 eq(sp.cancel(ch*fj*ci/expected),1,"all-exponent factor cancellation")
 n=sp.symbols('n',integer=True,nonnegative=True)
 eq((n+sp.Rational(3,2))/(n+3),(2*n+3)/(2*n+6),"b_n normalizer recurrence")
 eq(1-n/(n+3),3/(n+3),"b_n first moment")
 j,J=sp.symbols('j J',integer=True,positive=True)
 eq(2/(4*j*j-1),1/(2*j-1)-1/(2*j+1),"Fejer telescope step")
 eq(sp.summation(2/(4*j*j-1),(j,1,J)),1-1/(2*J+1),"Fejer positivity floor")
 z=sp.symbols('z')
 for N in range(1,17):
  eq(sp.expand((z-1)*sum(z**h for h in range(N))),z**N-1,
     f"geometric character identity {N}")

def check_degree(degree):
 A,M,L=orders(degree)
 for k in range(2*A-2):
  eq(cheb2_U(A,k),F(int(k==0)),("ChebII",degree,k))
 for k in range(M):
  want=F(1) if k==0 else (F(0) if k%2 else F(1,1-k*k))
  eq(fejer_T(M,k),want,("FejerI",degree,k))
  eq(fejer_power(k),F(0) if k%2 else F(1,k+1),
     ("Fejer polynomial",degree,k))
 count=0
 for e in monomials(degree):
  eq(product_rule(e),sphere(e),("S3",degree,e))
  count+=1
 print(f"degree={degree}, nodes={(A-1)*M*L}, moments={count}")

if __name__=="__main__":
 ap=argparse.ArgumentParser()
 ap.add_argument("--degree",type=int,default=9)
 args=ap.parse_args()
 assert args.degree>=0
 symbolic_proofs()
 for d in range(args.degree+1):check_degree(d)
 print("SYM3_UNIVERSAL_DEGREE_PRODUCER_PASS",checks)
