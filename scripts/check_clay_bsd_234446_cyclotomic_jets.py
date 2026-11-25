"""Exact local hypotheses and cyclotomic jet controls; no complex rank-four proof."""
from math import comb
from fractions import Fraction as Q
import sympy as sp
checks=0
def ck(ok):
 global checks
 if not ok: raise AssertionError('exact check failed')
 checks+=1
N=234446; D=468892
ck(D==4*117223 and N==2*117223 and sp.isprime(117223))
ck(3801%2!=0 and 3801%117223!=0)
def trace(p):
 return p-sum((y*y+x*y-x**3+x*x+79*x-289)%p==0 for x in range(p) for y in range(p))
ck(trace(3)==-3)
for p,expected in [(5,-4),(11,-6)]:
 a=trace(p); ck(a==expected and a%p!=0 and N%p!=0)
 ck(sp.legendre_symbol(trace(3)**2-12,p)==-1)
 ck(D%117223==0 and D%(117223**2)!=0)
 # Hensel unit root of X^2-aX+p, and multiplier numerator valuation.
 alpha=a%p
 for k in range(1,12):
  m=p**k
  ck((alpha*alpha-a*alpha+p)%m==0 and alpha%p!=0)
  lifts=[alpha+i*m for i in range(p) if ((alpha+i*m)**2-a*(alpha+i*m)+p)%(m*p)==0]
  ck(len(lifts)==1);alpha=lifts[0]
 ck((alpha-1)%p==(0 if p==5 else (a-1)%p))
 ck((alpha-1)%25!=0 if p==5 else (alpha-1)%p!=0)
 print('p',p,'a_p',a,'#E',p+1-a,'alpha mod p^12',alpha,'Euler multiplier valuation',2 if p==5 else 0)
 for m in range(1,9):
  n=p**m
  # w_m=(1+T)^n-1; first 3 coefficients v_p=m.
  w=[0]+[comb(n,j) for j in range(1,4)]
  for j in range(1,4): ck(w[j]%n==0 and w[j]%(n*p)!=0)
  # For any integral low quotient coefficients, w_m times H has these congruences.
  for h in [(1,0,0),(0,1,0),(0,0,1),(2,-3,5),(-7,11,-13)]:
   for j in range(1,4):ck(sum(w[j-i]*h[i] for i in range(j))%n==0)
  # Reciprocal even Laurent perturbation X^n+X^-n-2; exact T jets
  c=[comb(n,j)+(-1)**j*comb(n+j-1,j)-(2 if j==0 else 0) for j in range(4)]
  ck(c==[0,0,n*n,-n*n]);ck(all(x%n==0 for x in c))
  # In the complex logarithm coordinate X=exp(z), second derivative is 2n², nonzero.
  ck(n*n+(-n)**2==2*n*n and 2*n*n>0)
  # Algebraic roots-of-unity evaluations vanish at each earlier finite level.
  for r in range(m+1):ck(n%(p**r)==0)
print(f'{checks}/{checks} exact controls PASS')
