"""Independent exact SymPy acceptance of the committed norm functions."""
from check_cm_cyclic_orbit_norm import cyclic_norm, diagonal_valuation_norm, split_moduli, root
from sympy import Poly, symbols, ZZ, Matrix, resultant
from sympy.polys.matrices import DomainMatrix
from random import Random
from itertools import islice
from math import gcd
x,q=symbols('x q'); rng=Random(9)
def mul(a,b,n,r):
 o=[0]*(n+1)
 for i,u in enumerate(a[:n+1]):
  for j,w in enumerate(b[:n+1-i]):o[i+j]=(o[i+j]+u*w)%r
 return o
def detnorm(h,p,n,r):
 a=[sum(h[i]*q**(i//p) for i in range(j,len(h),p)) for j in range(p)]
 m=Matrix(p,p,lambda i,j:a[(i-j)%p]*(q if i<j else 1))
 d=Poly(DomainMatrix.from_Matrix(m).det().as_expr(),q,domain=ZZ)
 z=Poly(resultant(x**p-q,sum(a[j]*x**j for j in range(p)),x),q,domain=ZZ)
 assert d==z
 return [int(d.nth(i))%r for i in range(n+1)]
def lognorm(h,p,n,r):
 l=[0]
 for k in range(1,p*n+1):l.append((k*h[k]-sum(h[i]*l[k-i] for i in range(1,k)))%r)
 a=[1]
 for k in range(1,n+1):a.append(sum(l[p*i]*a[k-i] for i in range(1,k+1))*pow(k,-1,r)%r)
 return a
c=d=v=0
for p in (3,5,7,11,17,41):
 for n in (1,2,3):
  for ell,r in islice(split_moduli(p,max(n,p*n//(p-1)),12),2):
   z=root(p,ell,r);h=[1]+[rng.randrange(-8,9) for _ in range(p*n)]
   a=cyclic_norm(h,p,n,r,z,mul);assert a==lognorm(h,p,n,r);c+=1
   if p<=7:assert a==detnorm(h,p,n,r);d+=1
   j=[1]+[rng.randrange(-8,9) for _ in range(n)];B=[1]+[rng.randrange(-8,9) for _ in range(p*n-p+1)];h=[0]*(p*n+1)
   for i,b in enumerate(j):h[p*i]+=b
   for i,b in enumerate(B):h[i+p-1]-=b
   assert diagonal_valuation_norm(h,j,p,n,r,mul)==cyclic_norm(h,p,n,r,z,mul);v+=1
print('PASS orbit/log',c,'SymPy determinant/resultant',d,'valuation',v)
try:diagonal_valuation_norm([],[],41,82,83**2,mul)
except ValueError:print('PASS nonunit rejection')
else:raise AssertionError
