"""234446.a1: exact two-crossing upper bound, NOT central second derivative vanishing."""
from math import isqrt, factorial
from fractions import Fraction as Q
import sympy as sp
N=234446; M=4000; checks=0

def check(ok,msg):
 global checks
 if not ok: raise AssertionError(msg)
 checks+=1

a1,a2,a3,a4,a6=1,-1,0,-79,289
b2=a1*a1+4*a2;b4=2*a4+a1*a3;b6=a3*a3+4*a6;b8=a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4
D=-b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
check(D==2*N and sp.isprime(117223) and (b2*b2-24*b4)%2!=0 and (b2*b2-24*b4)%117223!=0,'minimal semistable conductor')
def trace(p):
 if p==2:return p-sum((y*y+x*y-x**3+x*x+79*x-289)%p==0 for x in range(p) for y in range(p))
 sq=[0]*p
 for x in range(1,p):sq[x*x%p]=1
 return sum(0 if (d:=(x*x+4*(x*x*x-x*x-79*x+289))%p)==0 else 1-2*sq[d] for x in range(p))
check(trace(2)==-1 and trace(117223)==1,'positive global sign')
ap={int(p):trace(int(p)) for p in sp.primerange(2,M+1)}
cs=[]
for n in range(1,M+1):
 a=1
 for p,e in sp.factorint(n).items():
  x,y=1,ap[p]
  for j in range(1,e):x,y=y,ap[p]*y-(0 if N%p==0 else p*x)
  a*=y
 cs.append(a)
R=Q(988,1000)
x=Q(628,48500)
check(485**2>N and sum(x**j/factorial(j) for j in range(5))>1/R,'upper qstar')
check(484**2<N and 1-Q(44,7*484)>Q(98,100),'lower qstar')
T0=2*R**M*((M+1)/(1-R)+R/(1-R)**2)
T1=2*R**(M-1)*(M*(M+1)/(1-R)+(2*M+1)*R/(1-R)**2+R*(1+R)/(1-R)**3)
S=10**25;den=10**6
ceil=lambda r:-(-r.numerator//r.denominator)
err0=ceil(S*T0);err1=ceil(S*T1)
# exact integer interval Horner with outward rounding
# A local coefficient prefix may be used ONLY with an independently bounded tail;
# here retain all M terms.
def enclosure(c,a,b):
 lo=hi=c[-1]*S
 for z in reversed(c[:-1]):
  v=lo*a,lo*b,hi*a,hi*b
  lo=min(v)//den+z*S
  hi=-((-max(v))//den)+z*S
 return lo,hi

def certify(c,a,b,sign,err):
 stack=[(a,b)]; accepted=0; gap=None
 while stack:
  l,r=stack.pop();lo,hi=enclosure(c,l,r)
  margin=lo-err if sign>0 else -hi-err
  if margin>0:
   check(True,'signed enclosure');accepted+=1;gap=margin if gap is None else min(gap,margin)
  else:
   check(r-l>1,'resolution exhausted')
   m=(l+r)//2;stack.extend(((l,m),(m,r)))
 print('accepted bins',a,b,sign,accepted,'minimum margin',float(Q(gap,S)),flush=True)
dc=[i*a for i,a in enumerate(cs) if i]
certify(dc,0,500000,-1,err1)
certify(cs,500000,900000,-1,err0)
certify(dc,900000,988000,1,err1)
lo,hi=enclosure(cs,980000,980000)
check(lo>err0,'positive terminal value before qstar')
print('tail bounds',float(T0),float(T1),flush=True)
# Independent lower bound by actual point reduction, not analytic rank input.
pts=[(-10,7),(-9,19),(-8,23),(-7,25)]
for x,y in pts:check(y*y+x*y==x*x*x-x*x-79*x+289,"actual rational point")
O=None
def add(P,Qp,l):
 if P is None:return Qp
 if Qp is None:return P
 x,y=P;u,v=Qp
 if x==u:
  if (y+v+x)%l==0:return None
  s=(3*x*x-2*x-79-y)*pow((2*y+x)%l,-1,l)%l
 else:s=(v-y)*pow((u-x)%l,-1,l)%l
 z=(s*s+s+1-x-u)%l
 return z,(-y-x+(s+1)*(x-z))%l
def mul(n,P,l):
 R=None
 while n:
  if n%2:R=add(R,P,l)
  P=add(P,P,l);n//=2
 return R
rows=[]
for l in (13,23,59,71):
 order=l+1-trace(l)
 check(order%5==0 and order%25!=0 and N%l!=0,'good reduction and exact 5 valuation')
 v=[mul(order//5,(x%l,y%l),l) for x,y in pts]
 G=next(P for P in v if P is not None)
 check(mul(5,G,l) is None,'order-five generator')
 row=[next(k for k in range(5) if mul(k,G,l)==P) for P in v]
 rows.append(row);print('local row',l,order,row)
det=int(sp.Matrix(rows).det())
check(det%5!=0,'point independence modulo five')
check((3+1-trace(3))%5!=0,'no rational five torsion')
print('determinant',det, f'{checks}/{checks} PASS')
