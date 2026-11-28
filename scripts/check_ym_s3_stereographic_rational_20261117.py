#!/usr/bin/env python3
"""Root-free, pi-free positive rational S3 midpoint sums and Cauchy bounds.

Exact SymPy polynomial identities, rational nodes and strict rational
probability weights. Analytic convergence uses elementary Lipschitz
midpoint estimates + rational product tail, not an assumed Haar
integral. Agda transitive kernel acceptance is a separate task.
"""
import sympy as s
from fractions import Fraction as F
from itertools import product

checks=0
def check(condition,label):
 global checks
 assert condition,label
 checks+=1

x,y,z,a,b,c=s.symbols('x y z a b c',real=True)
t=s.Matrix([x,y,z]);u=s.Matrix([a,b,c])
r=t.dot(t);rr=u.dot(u);d=1+r
V=s.Matrix([1-r,2*x,2*y,2*z])
W=s.Matrix([1-rr,2*a,2*b,2*c])
check(s.expand(V.dot(V)-d*d)==0,'Pythagorean numerator')
chord_num=sum((V[i]*(1+rr)-W[i]*d)**2 for i in range(4))
check(s.expand(chord_num-4*((t-u).dot(t-u))*d*(1+rr))==0,
      'exact rational chord metric')
for i in range(3):
 for j in range(3):
  ti=t[i];tj=t[j]
  vi=[-4*ti]+[2*(d if m==i else 0)-4*t[m]*ti for m in range(3)]
  vj=[-4*tj]+[2*(d if m==j else 0)-4*t[m]*tj for m in range(3)]
  check(s.expand(sum(vi[m]*vj[m] for m in range(4))-
       (4*d*d if i==j else 0))==0,'stereographic metric')
# Round metric is 4/(1+r)^2 I3. Positive area density is 8/(1+r)^3.

def point(v):
 r=sum(i*i for i in v);d=1+r
 return ((1-r)/d,)+tuple(2*i/d for i in v)
def density(v):
 return F(8)/(1+sum(i*i for i in v))**3
def quadrature(R,N):
 h=F(2*R,N)
 grid=[-R+(F(j)+F(1,2))*h for j in range(N)]
 nodes=[]
 for v in product(grid,repeat=3):
  p=point(v);w=h**3*density(v)
  check(sum(q*q for q in p)==1,'source rational sphere node')
  check(w>0,'positive unnormalised area weight')
  nodes.append((p,w))
 total=sum((w for p,w in nodes),F(0))
 check(total>0,'total positive')
 return [(p,w/total) for p,w in nodes]

def estimate(k,B,L):
 assert k>=0 and B>=0 and L>=0
 C=(B+L+1).__ceil__()
 R=2**(k+16)*C
 h=F(1,R**5)
 # Product bound: J<=8/prod_i(1+t_i^2); tail <=768/R.
 # |grad J|<=48, |Dphi|<=2, cube midpoint distance<=h.
 e0=F(768,R)+384*R**3*h
 ef=B*F(768,R)+8*R**3*h*(48*B+16*L)
 check(e0<F(1,2),'finite mass anchored by full area>=1')
 error=2*(ef+B*e0)
 check(error<=F(1,2**(k+3)),'fast Cauchy error envelope')
 return R,h,error

for R,N in ((F(1),2),(F(1),4),(F(2),6),(F(3),6)):
 nodes=quadrature(R,N)
 check(sum(w for p,w in nodes)==1,'normalized positive sum')
 for i in range(1,4):
  check(sum(w*p[i] for p,w in nodes)==0,'signed reflection')
  check(sum(w*p[i]**2 for p,w in nodes)==
        sum(w*p[1]**2 for p,w in nodes),'axis exchange')
 print('cube',R,'sidepoints',N,'nodes',len(nodes))
for B,L in ((F(1),F(1)),(F(3,2),F(7,4)),(F(0),F(5))):
 for k in range(12):
  estimate(k,B,L)
print('RATIONAL_STEREOGRAPHIC_S3_CERTIFICATE_PASS',checks)
