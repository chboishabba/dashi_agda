#!/usr/bin/env python3
"""Finite shift-two Fourier identity and signed shell no-promotion regression."""
import cmath, math
def dft(a):
 m=len(a)
 return [sum(a[n]*cmath.exp(-2j*math.pi*k*n/m) for n in range(m)) for k in range(m)]
def check(a):
 m=len(a); f=dft(a)
 direct=sum(a[n]*a[(n+2)%m] for n in range(m))
 terms=[abs(f[k])**2*cmath.exp(-4j*math.pi*k/m)/m for k in range(m)]
 assert abs(sum(terms)-direct)<1e-8
 shells=[0.,0.,0.]
 for k,t in enumerate(terms):
  d=min(k,m-k); j=0 if d<=1 else 1 if d<=m//4 else 2
  shells[j]+=t.real
 assert abs(sum(shells)-direct)<1e-8
 return round(direct,8),[round(x,8) for x in shells]
def vm(n):
 for p in range(2,n+1):
  if n%p==0:
   q=n
   while q%p==0:q//=p
   return math.log(p) if q==1 else 0.
 return 0.
if __name__=="__main__":
 for x,m in [(10,32),(20,64),(40,128)]:
  a=[vm(n) if 2<=n<=x else 0. for n in range(m)]
  print("Mangoldt",x,m,check(a))
 for a in ([1.,0.,0.,0.,0.,0.,0.,0.],[1.,1.,0.,0.,0.,0.,0.,0.]):
  v,s=check(a); assert v==0 and any(t<0 for t in s)
  print("spectral-cancellation",v,s)
