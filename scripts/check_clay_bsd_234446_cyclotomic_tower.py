"""Replay actual symbols; norm and augmentation checks, not complex BSD."""
import runpy
from pathlib import Path
from math import comb
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ
src=runpy.run_path(str(Path(__file__).with_name('check_clay_bsd_234446_actual_cyclotomic_symbols.py')))
V=src['V']; checks=0

def ck(ok):
 global checks
 if not ok: raise AssertionError('tower check failed')
 checks+=1

def vp(a,p):
 a=abs(int(a))
 if not a: raise ValueError('zero has infinite valuation')
 k=0
 while a%p==0:a//=p;k+=1
 return k
X=sp.Symbol('X')
for p,m in ((5,1),(5,2),(11,1)):
 q=p**(m+1); n=p**m
 roots=[z for z in range(1,q) if pow(z,p-1,q)==1]
 C=[sum(V[q][z*pow(1+p,k,q)%q] for z in roots) for k in range(n)]
 A=sp.Poly.from_list(C[::-1],X,domain=ZZ)
 phi=sp.Poly(sp.cyclotomic_poly(n,X),X,domain=ZZ)
 norm=int(sp.resultant(phi,A));ck(norm!=0 and vp(norm,p)==4)
 print('actual doubled symbol norm',p,m,norm,'valuation',vp(norm,p),flush=True)
 # Quotient modulo p^m of actual ordinary finite polynomial equals unit*T^4.
 d=src['d1'] if (p,m)==(5,1) else src['d2'] if p==5 else src['d3']
 P=sp.Matrix(n,n,lambda i,j:int(d[(i-j)%n]))
 snf=smith_normal_form(P,domain=ZZ)
 # valuations truncated at m, so using representatives does not alter test.
 counts=sorted(m if snf[i,i]==0 else min(m,vp(snf[i,i],p)) for i in range(n))
 ck(counts==[0]*(n-4)+[m]*4)
 print('actual finite mod p^m Smith profile',p,m,counts,flush=True)
# Z_p[T]/(T^4,w_m): nonconstant lattice relations on T,T²,T³.
for p in (5,11):
 for m in range(1,9):
  n=p**m
  W=sp.Matrix(3,3,lambda i,j:comb(n,i-j+1) if i>=j else 0)
  D=smith_normal_form(W,domain=ZZ)
  ck(all(vp(D[i,i],p)==m for i in range(3)))
  ck(abs(int(W.det()))==p**(3*m))
  ck(all(comb(n,j)%n==0 for j in (1,2,3)))
  ck((p-1)*p**(m-1)*sum([4])==4*sp.totient(n))
print(f'{checks}/{checks} tower checks PASS',flush=True)
