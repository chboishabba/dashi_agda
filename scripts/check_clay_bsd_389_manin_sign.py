"""389.a1: exact mod-5 Manin symbol replay and rational sign enclosure.
Period scale uses Kim section 8 nonvanishing; no native theorem checking.
"""
from fractions import Fraction as Q
from math import gcd
import sympy as sp
from collections import defaultdict
N=389;p=5
checks=0
def check(ok,msg):
 global checks
 if not ok: raise AssertionError(msg)
 checks+=1
# projective bottom rows normalized to (c,1) or (1,0)
def idx(c,d):
 c%=N;d%=N
 if d:return c*pow(d,-1,N)%N
 if not c: raise ValueError('zero row')
 return N

def addrow(terms):
 r={}
 for i,a in terms:
  r[i]=(r.get(i,0)+a)%p
 return {i:a for i,a in r.items() if a}
# Manin symbol {g0,g infinity}; orientation path infinity -> r via continued fractions
from functools import lru_cache
@lru_cache(None)
def path(r):
 if r is None:return {}
 a,b=r.numerator,r.denominator
 pp,p0=0,1;qq,q0=1,0
 out=defaultdict(int)
 while b:
  k,a,b=a//b,b,a%b
  pn,qn=k*p0+pp,k*q0+qq
  det=pn*q0-p0*qn
  if det not in (-1,1):raise ValueError(det)
  out[idx(qn,det*q0)]+=1
  pp,p0=p0,pn;qq,q0=q0,qn
 return dict(out)
def edge(r,s): # {r,s}
 return list(path(s).items())+[(i,-a) for i,a in path(r).items()]
def point(a,b):return Q(a,b) if b else None
def transform(r,l,b=None):
 if r is None:return None
 return l*r if b is None else (r+b)/l
# lift bottom row (c,1) with matrix [[1,0],[c,1]], (1,0) S
rows=[]
for i in range(N+1):
 c,d=(i,1) if i<N else (1,0)
 rows.extend([addrow([(i,1),(idx(d,-c),1)]),addrow([(i,1),(idx(d,-c-d),1),(idx(-c-d,c),1)]),addrow([(i,1),(idx(-c,d),-1)])])
 # cusp pair g0,g infinity
 r,s=(Q(0),point(1,c)) if i<N else (None,Q(0))
 for l in (2,3,5,7,11):
  # recompute traces rather than trust literals
  al=l+1-(1+sum((y*y+y-x*x*x-x*x+2*x)%l==0 for x in range(l) for y in range(l)))
  terms=[(i,-al)]+edge(transform(r,l),transform(s,l))
  for b in range(l):terms+=edge(transform(r,l,b),transform(s,l,b))
  rows.append(addrow(terms))
# sparse row echelon
piv={}
for original in rows:
 r=original.copy()
 while r:
  j=min(r); a=r[j]
  if j not in piv:
   v=pow(a,-1,p);piv[j]={k:x*v%p for k,x in r.items()};break
  for k,x in piv[j].items():
   y=(r.get(k,0)-a*x)%p
   if y:r[k]=y
   elif k in r:del r[k]
free=sorted(set(range(N+1))-set(piv));print('dimension',len(free),free,flush=True)
check(len(free)==1,"eigenspace dimension")
vec=[0]*(N+1);vec[free[0]]=1
for j in sorted(piv,reverse=True):vec[j]=(-sum(v*vec[k] for k,v in piv[j].items() if k!=j))%p
for r in rows: check(sum(a*vec[j] for j,a in r.items())%p==0,"original Manin/Hecke relation")
# lambda(r)=- path(infinity->r) up to nonzero scalar, sign irrelevant
sym=lambda r:-sum(a*vec[i] for i,a in path(r).items())%p
l1,l2=41,61
logs={}
for l in (l1,l2):
 g=int(sp.primitive_root(l));logs[l]={pow(g,k,l):k%p for k in range(l-1)}
 order=1+sum((y*y+y-x*x*x-x*x+2*x)%l==0 for x in range(l) for y in range(l))
 check((l-1)%p==0 and order%p==0,"Kolyvagin prime")
 print("prime",l,"root",g,"#E",order,flush=True)
D=sum(sym(Q(a,l1*l2))*logs[l1][a%l1]*logs[l2][a%l2] for a in range(1,l1*l2) if gcd(a,l1*l2)==1)%p
print('delta normalized line',D, 'central',sym(Q(0)),flush=True)
check(D==3,"nonzero normalized Kurihara contraction")
check(sym(Q(0))==0,"central symbol vanishes mod5 only")
# q coefficient sign isolation using exact integer point counts, multiplicativity
M=160
ap={}
for l in sp.primerange(2,M+1):
 l=int(l); counts=[0]*l
 for y in range(l):counts[(y*y+y)%l]+=1
 ap[l]=l-sum(counts[(x*x*x+x*x-2*x)%l] for x in range(l))
def coeff(n):
 result=1
 for l,e in sp.factorint(n).items():
  a,b=1,ap[l]
  for _ in range(1,e):a,b=b,ap[l]*b-l*a
  result*=b
 return result
cs=[coeff(n) for n in range(1,M+1)]
R=Q(73,100)
# sum_{j>=M} 2(j+1)j R^(j-1)
T=2*R**(M-1)*(M*(M+1)/(1-R)+(2*M+1)*R/(1-R)**2+R*(1+R)/(1-R)**3)
# bound using interval Horner on 73 bins, derivative coefficients.
dc=[i*a for i,a in enumerate(cs) if i]
def horner_interval(c,a,b):
 lo=hi=Q(c[-1])
 for z in reversed(c[:-1]):
  v=(lo*a,lo*b,hi*a,hi*b)
  lo,hi=min(v)+z,max(v)+z
 return lo,hi
bounds=[horner_interval(dc,Q(i,100),Q(i+1,100))[1]+T for i in range(73)]
for bound in bounds: check(bound < -1,"strict derivative enclosure")
upper=max(bounds)
print('tail derivative bound',float(T),'max derivative upper',float(upper))
check(upper<0,'global derivative strictly negative')
# q<=0.73 using pi>3.14, sqrt389<19.73 and exp positive Taylor
x=Q(628,1973)
check(Q(1973,100)**2>389 and sum(x**j/sp.factorial(j) for j in range(5))>Q(100,73),'q cutoff')
# discriminant and bad trace
b2,b4,b6,b8=4,-4,1,-3
# b8 = a2*a3^2-a4^2=1-4=-3
Delta=-b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
check(Delta==389,'discriminant')
c4=b2*b2-24*b4
check(c4%389!=0,'multiplicative reduction')
q=389
counts=[0]*q
for y in range(q):counts[(y*y+y)%q]+=1
bad_a=q-sum(counts[(x*x*x+x*x-2*x)%q] for x in range(q))
check(bad_a==1,'root sign')
check((ap[3]**2-4*3)%5 in (2,3),"irreducible mod5 Frobenius at 3")
# exact group law on original y²+y=x³+x²−2x over F_l
O=None
def plus(P,Qp,l):
 if P is None:return Qp
 if Qp is None:return P
 x,y=P;u,v=Qp
 if x==u:
  if (y+v+1)%l==0:return None
  s=(3*x*x+2*x-2)*pow((2*y+1)%l,-1,l)%l
 else:s=(v-y)*pow((u-x)%l,-1,l)%l
 z=(s*s-1-x-u)%l
 return z,(-1-y+s*(x-z))%l
def mul(n,P,l):
 R=None
 while n:
  if n%2:R=plus(R,P,l)
  P=plus(P,P,l);n//=2
 return R
P=(0,0);Qp=(1,0)
mat=[]
for l,order in [(41,45),(61,70)]:
 u,v=mul(order//5,P,l),mul(order//5,Qp,l)
 G=u if u is not None else v
 check(G is not None and mul(5,G,l) is None,'nonzero order5')
 row=[next(k for k in range(5) if mul(k,G,l)==z) for z in (u,v)]
 mat.append(row);print('local row',l,row)
check((mat[0][0]*mat[1][1]-mat[0][1]*mat[1][0])%5!=0,'independent mod5')
# no rational 5-torsion by good reduction mod3
check((1+sum((y*y+y-x*x*x-x*x+2*x)%3==0 for x in range(3) for y in range(3)))%5!=0,'no 5 torsion')
print(f'{checks}/{checks} PASS exact analytic one-crossing and arithmetic localization')
