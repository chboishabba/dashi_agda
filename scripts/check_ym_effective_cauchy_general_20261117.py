#!/usr/bin/env python3
"""Exact rational Bishop-real Q_n fast-Cauchy schedule CERTIFICATE.

Given user-supplied B>=0, L>0, and positive exact cubatures of degree
n_k+1, Q_n approximates an L-Lipschitz bounded |f|<=B by
 L*delta + 12*B/((n+3)*delta²).
n_k=ceil(96*B*L²/eps_k³), eps_k=2^(-k-3).
The script verifies exact rational inequalities for arbitrary k, B, L.
It does not invent the Bishop modulus / cubature source proofs.
"""
from fractions import Fraction as Q
import argparse

def schedule(k,B,L):
 assert isinstance(k,int) and k>=0 and B>=0 and L>0
 eps=Q(1,2**(k+3)); delta=eps/(2*L)
 target=Q(96)*B*L**2/eps**3
 n=(target.numerator+target.denominator-1)//target.denominator
 actual=L*delta+Q(12)*B/((n+3)*delta**2)
 assert actual<=eps
 return n,eps,delta,actual

def generic_cauchy(j,k,B,L):
 assert j>=k>=0
 nj,ej,dj,errj=schedule(j,B,L)
 nk,ek,dk,errk=schedule(k,B,L)
 # Contractivity |H(Q_nj)-H(Q_nk)| <= ej + ek;
 # monotonicity of dyadic eps gives <= 2^-k-2.
 assert ej+ek<=Q(1,2**(k+2))
 return ej+ek

if __name__=="__main__":
 ap=argparse.ArgumentParser()
 ap.add_argument("--bound",default="7/5")
 ap.add_argument("--lip",default="3/4")
 ap.add_argument("--levels",type=int,default=16)
 args=ap.parse_args()
 B,L=Q(args.bound),Q(args.lip)
 checks=0
 for k in range(args.levels):
  n,eps,delta,err=schedule(k,B,L);checks+=1
  for j in range(k,args.levels):
   generic_cauchy(j,k,B,L);checks+=1
  if k<5:print(f"k={k} n={n} delta={delta} uniform_error<={eps}")
 print(f"YM_REAL_EFFECTIVE_BISHOP_CAUCHY_SCHEDULE_PASS={checks}")
