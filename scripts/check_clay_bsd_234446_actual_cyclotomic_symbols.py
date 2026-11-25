"""Actual 234446a1 modular symbols via Fricke split and exact rational enclosures.
Requires classical modularity, optimal Manin constant one, and rational torsion zero.
Integer symbols use the least positive real period. Divide by two for
Stein--Wuthrich normalization (two real components).
"""
from fractions import Fraction as Q
from math import isqrt, factorial, gcd, comb
import numpy as np
import sympy as sp
N=234446; S=10**24; M=150000
checks=0
def ck(x):
 global checks
 if not x: raise AssertionError('certificate failed')
 checks+=1
ceil=lambda x:-((-x.numerator)//x.denominator)
fl=lambda x:x.numerator//x.denominator
def atan_bounds(k):
 a=sum((Q((-1)**i,(2*i+1)*k**(2*i+1)) for i in range(40)),Q(0))
 return a,a+Q(1,81*k**81)
l,h=atan_bounds(5);u,v=atan_bounds(239)
pi=(16*l-4*v,16*h-4*u)
def sqrt_bounds(x):
 z=isqrt(fl(x*S*S));return Q(z,S),Q(z+1,S)
ns=sqrt_bounds(Q(N))
def exp_neg(x):
 a=sum(((-x)**i/factorial(i) for i in range(14)),Q(0));return a,a+x**14/factorial(14)
def cos_bounds(x):
 a=sum(((-1)**i*x**(2*i)/factorial(2*i) for i in range(16)),Q(0));return a,a+x**32/factorial(32)
# The three roots of 4x^3-3x^2-316x+1156 are isolated by these brackets.
def cubic(x):return 4*x**3-3*x*x-316*x+1156
def root(a,b):
 a,b=Q(a),Q(b);ck(cubic(a)*cubic(b)<0)
 for _ in range(85):
  t=(a+b)/2
  if cubic(a)*cubic(t)<=0:b=t
  else:a=t
 return a,b
# rational root isolation brackets obtained directly from sign changes
roots=[root(-11,-10),root(5,Q(21,4)),root(Q(21,4),6)]
# Omega = pi / AGM(sqrt(e1-e3),sqrt(e1-e2)), least real period.
lo3,hi3=roots[0];lo2,hi2=roots[1];lo1,hi1=roots[2]
a=sqrt_bounds(lo1-hi3)[0],sqrt_bounds(hi1-lo3)[1]
b=sqrt_bounds(lo1-hi2)[0],sqrt_bounds(hi1-lo2)[1]
for _ in range(8):
 a,b=((a[0]+b[0])/2,(a[1]+b[1])/2),(sqrt_bounds(a[0]*b[0])[0],sqrt_bounds(a[1]*b[1])[1])
om=(pi[0]/a[1],pi[1]/b[0]);print('period interval',float(om[0]),float(om[1]),flush=True)
ck(om[1]-om[0]<Q(1,10**18))
# Exact point counts using vectorized integer arithmetic (no floating FFT).
def trace(p):
 if p==2:return p-sum((y*y+x*y-x**3+x*x+79*x-289)%p==0 for x in range(p) for y in range(p))
 x=np.arange(p,dtype=np.int64);z=np.zeros(p,dtype=np.int8);z[x*x%p]=1;z[0]=0
 d=(4*x*x*x-3*x*x-316*x+1156)%p
 return int(np.count_nonzero(d)-2*int(z[d].sum(dtype=np.int64)))
ck(M**3*4<2**63)
ck(trace(3)==-3 and trace(5)==-4 and trace(11)==-6)
# E(Q)_tors=0 by good reductions at 3,5 (prime-to-residue characteristic
# injection, use an additional good prime 7 to remove any ambiguity).
orders=[p+1-trace(p) for p in (3,5,7)];ck(gcd(orders[0],orders[1])==1)
ck(trace(2)==-1 and trace(117223)==1)
cs=[0]*(M+1);cs[1]=1
for p in sp.primerange(2,M+1):
 p=int(p);ap=trace(p);v=p;prev=1;cur=ap
 while v<=M:
  cs[v]=cur
  prev,cur=cur,ap*cur-(0 if N%p==0 else p*prev);v*=p
# Multiplicative assembly using smallest prime factors.
spf=list(range(M+1))
for p in sp.primerange(2,isqrt(M)+1):
 p=int(p)
 for k in range(p*p,M+1,p):
  if spf[k]==k:spf[k]=p
for n in range(2,M+1):
 p=spf[n];k=n;v=1
 while k%p==0:k//=p;v*=p
 if k>1:cs[n]=cs[v]*cs[k]
ck(cs[1]==1 and all(abs(a)<=2*n for n,a in enumerate(cs) if n))
print('coefficients ready',M,flush=True)
def symbols(q):
 # y=1/(q sqrt N); r=exp(-2pi*y), all primitive terms absolute <=2 r^n.
 xlo=2*pi[0]/(q*ns[1]);xhi=2*pi[1]/(q*ns[0]);rlo=exp_neg(xhi)[0];rhi=exp_neg(xlo)[1]
 rl,rh=fl(rlo*S),ceil(rhi*S);lo=hi=S
 B=[[0,0] for _ in range(q)]
 for n in range(1,M+1):
  lo=lo*rl//S;hi=-(-hi*rh//S)
  a=cs[n];i=n%q
  B[i][0]+=min(a*lo,a*hi)//n;B[i][1]+=-(-max(a*lo,a*hi)//n)
 # upper bound r^(M+1) using current outward-rounded hi, avoid giant fractions
 tail=Q(2*hi*rh,S*(S-rh));ck(tail< Q(1,10))
 C=[]
 for k in range(q):
  j=min(k,q-k);xl=2*pi[0]*j/q;xh=2*pi[1]*j/q
  C.append((fl(cos_bounds(xh)[0]*S),ceil(cos_bounds(xl)[1]*S)))
 def realA(a):
  l=h=0
  for i,(b,c) in enumerate(B):
   u,v=C[a*i%q];z=(b*u,b*v,c*u,c*v);l+=min(z)//S;h+=-(-max(z)//S)
  return Q(l,S)-tail,Q(h,S)+tail
 vals={0:0}
 for a in range(1,q):
  if gcd(a,q)>1:continue
  d=pow(a*N,-1,q)
  l,h=realA(a);u,v=realA(-d%q)
  # Since cusp maps to O, real part is integral multiple of least real period.
  # positive discriminant => rectangular period lattice.
  z=[(l+u)/om[0],(l+u)/om[1],(h+v)/om[0],(h+v)/om[1]]
  low,high=ceil(min(z)),fl(max(z));ck(low==high);vals[a]=low
 ck(all(vals[a]==vals[-a%q] for a in vals))
 print('q',q,'symbols',len(vals)-1,'tail',float(tail),'range',min(vals.values()),max(vals.values()),flush=True)
 return vals
V={q:symbols(q) for q in (5,25,125,11,121)}
def finite(p,m):
 n=m+1;q=p**n;mod=p**(m+3);a=cs[p];alpha=a%p
 for j in range(1,m+3):
  t=p**j;alpha=next(alpha+k*t for k in range(p) if ((alpha+k*t)**2-a*(alpha+k*t)+p)%(t*p)==0)
 u=pow(alpha,-1,mod);g=1+p;d=[]
 roots=[x for x in range(1,q) if pow(x,p-1,q)==1];ck(len(roots)==p-1)
 for k in range(p**m):
  c=0
  for z in roots:
   x=z*pow(g,k,q)%q;c+=pow(u,n,mod)*V[q][x]-pow(u,n+1,mod)*V[q//p][x%(q//p)]
  d.append((c*pow(2,-1,mod))%mod)
 moments=[sum(comb(k,j)*a for k,a in enumerate(d))%mod for j in range(5)]
 ck(all(x%p**m==0 for x in moments[:4]))
 ck(moments[4]%p == (1 if p==5 else 2))
 print('p,m',p,m,'moments mod',mod,moments,'fourth mod p^m',moments[4]%p**m,'distribution mod p^m',[a%p**m for a in d],flush=True)
 return d,mod
# Exact integral symbol Hecke distribution relation at each available level.
for p,m in ((5,1),(5,2),(11,1)):
 q=p**m
 for x in V[q]:
  if x==0:continue
  ck(sum(V[q*p][x+b*q] for b in range(p))==cs[p]*V[q][x]-(0 if m==1 else V[q//p][x%(q//p)]))
d1,mod1=finite(5,1);d2,mod2=finite(5,2);d3,mod3=finite(11,1)
for k in range(5):ck(sum(d2[k+5*j] for j in range(5))%mod1==d1[k])
print(checks,'checks PASS')
