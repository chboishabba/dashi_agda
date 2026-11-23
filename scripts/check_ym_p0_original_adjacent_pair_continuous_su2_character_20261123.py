#!/usr/bin/env python3
"""Original 4D Wilson L4 SU2 two adjacent F19 Haar fibres: all-beta character series.

No CMP119/122 constrained T, no full 960-fibre Wilson Haar integration,
no absolute W3 or same-H continuum claim. Exact native Wilson action,
unique F and G, full 1536 faces, and genuine continuous Haar on SU2^2.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial
from functools import lru_cache
from random import Random
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
import sympy as s
import mpmath as mp

src_path=Path(__file__).with_name('check_ym_p0_original_wilson_marked_ordered_t_20261123.py')
assert src_path.is_file(), 'Require the original full Wilson L4 source owner'
sp=spec_from_file_location('original_wilson',src_path)
src=module_from_spec(sp); sp.loader.exec_module(src)
checks=dict(geometry=0,source=0,symbolic=0,series=0,marked=0,tail=0)
assert (len(src.links),len(src.faces))==(1024,1536)
checks['geometry']+=1
origin=(0,0,0,0)
y=((origin,2),(src.step(origin,2),2))
z=((origin,3),(src.step(origin,3),3))
assert set(y+z)<=src.selected
assert len(set(y+z))==4
checks['geometry']+=2
A=set(k for k,f in enumerate(src.faces) if any(l in f for l in y))
B=set(k for k,f in enumerate(src.faces) if any(l in f for l in z))
assert len(A)==len(B)==12 and len(A&B)==1
assert (len(A-B),len(B-A),len(A&B),len(set(range(1536))-(A|B)))==(11,11,1,1513)
assert src.faces[next(iter(A&B))]==src.face(origin,2,3)
checks['geometry']+=4

one=(Q(1),Q(0),Q(0),Q(0))
def mul(p,q):
 a,b,c,d=p;e,f,g,h=q
 return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def inv(p):return (p[0],-p[1],-p[2],-p[3])
def dot(p,q):return sum((x*v for x,v in zip(p,q)),Q(0))
def field(q,r):return {y[0]:inv(q),y[1]:q,z[0]:inv(r),z[1]:r}
def plaq(u,f):
 a,b,c,d=f
 return mul(mul(mul(u.get(a,one),u.get(b,one)),inv(u.get(c,one))),inv(u.get(d,one)))
def original_action(u):return sum((1-plaq(u,f)[0] for f in src.faces),Q(0))
def source_marks(u):
 return (1-plaq(u,src.face(src.F,2,3))[0],
         1-plaq(u,src.face(src.G,2,3))[0])

rational_quaternions=[one,(-one[0],one[1],one[2],one[3]),
 (Q(0),Q(1),Q(0),Q(0)),(Q(0),Q(0),Q(1),Q(0)),
 (Q(0),Q(0),Q(0),Q(1)),(Q(3,5),Q(4,5),Q(0),Q(0)),
 (Q(3,5),Q(0),Q(4,5),Q(0)),(Q(0),Q(3,5),Q(4,5),Q(0)),
 (Q(1,2),)*4]
assert all(dot(q,q)==1 for q in rational_quaternions)
assert mul(rational_quaternions[2],rational_quaternions[3])==rational_quaternions[4]
assert mul(rational_quaternions[3],rational_quaternions[2])!=rational_quaternions[4]
checks['source']+=3
for q in rational_quaternions:
 for r in rational_quaternions:
  u=field(q,r)
  actual=original_action(u)
  expected=23-11*q[0]-11*r[0]-dot(q,r)
  assert actual==expected
  F,G=source_marks(u)
  assert F==1-dot(q,r) and G==0
  assert 0<=F<=2
  checks['source']+=3

# All-degree exact SU2 character expansion:
# f_x(g)=exp(x*ReTr(g)/2)=sum_n a_n(x) chi_n(g),
# a_n(x)=2(n+1)I_{n+1}(x)/x. Haar convolution gives
# int_SU2^2 f_a(V)f_b(W)f_c(V^-1 W) dVdW
#     =sum_n a_n(a)*a_n(b)*a_n(c)/(n+1).
# This is not the product a0(a)a0(b)a0(c): n>=1 terms are genuine.

@lru_cache(None)
def a_coeff(n,k):
 # coefficient of x^(n+2k) in a_n(x)
 return Q(n+1,2**(n+2*k)*factorial(k)*factorial(n+k+1))
def apoly(n,scale,deg):
 return {n+2*k: a_coeff(n,k)*scale**(n+2*k)
         for k in range((deg-n)//2+1)} if n<=deg else {}
def multiply(p,q,deg):
 out={}
 for i,pi in p.items():
  for j,qj in q.items():
   if i+j<=deg:out[i+j]=out.get(i+j,Q(0))+pi*qj
 return out
def character_series(deg,marked=False):
 out={i:Q(0) for i in range(deg+1)}
 for n in range(deg+1):
  an=apoly(n,Q(11),deg)
  ac=apoly(n,Q(1),deg+1)
  if marked:
   deriv={i-1:i*v for i,v in ac.items() if i>=1}
   for j,v in deriv.items():ac[j]=ac.get(j,Q(0))-v
  tr=multiply(multiply(an,an,deg),ac,deg)
  for i,v in tr.items():out[i]+=v/Q(n+1)
 return out

def poch(x,k):
 v=Q(1)
 for j in range(k):v*=Q(x+j)
 return v
@lru_cache(None)
def sphere(moment):
 if any(v%2 for v in moment):return Q(0)
 return (Q(1) if not any(moment) else
         Q(1)*__import__('functools').reduce(lambda a,b:a*b,
                (poch(Q(1,2),v//2) for v in moment),Q(1))
         /poch(Q(2),sum(moment)//2))
@lru_cache(None)
def direct_moment(i,j,k,mark_power):
 # Independent SU2 Haar quaternions q,r in S3. A=q0, B=r0, D=q dot r.
 # binomial multinomial expansion of D^k.
 out=Q(0)
 for x0 in range(k+1):
  for x1 in range(k-x0+1):
   for x2 in range(k-x0-x1+1):
    x3=k-x0-x1-x2
    xs=(x0,x1,x2,x3)
    cm=Q(factorial(k),factorial(x0)*factorial(x1)*factorial(x2)*factorial(x3))
    out+=cm*sphere((x0+i,x1,x2,x3))*sphere((x0+j,x1,x2,x3))
 if mark_power==1:return out-direct_moment(i,j,k+1,0)
 return out

def direct_series(deg,marked=False):
 out={m:Q(0) for m in range(deg+1)}
 for m in range(deg+1):
  for i in range(m+1):
   for j in range(m-i+1):
    k=m-i-j
    v=Q(11**(i+j),factorial(i)*factorial(j)*factorial(k))*direct_moment(i,j,k,int(marked))
    out[m]+=v
 return out

for marked in [False,True]:
 degree=9
 Acoef=character_series(degree,marked)
 Bcoef=direct_series(degree,marked)
 for n in range(degree+1):
  assert Acoef[n]==Bcoef[n],(marked,n,Acoef[n],Bcoef[n])
  checks['series']+=1
 if marked:
  assert Acoef[0]==1 and Acoef[1]<0
  checks['marked']+=2
 else:
  assert Acoef[0]==1 and Acoef[1]==0
  checks['series']+=2

# Nonfactorizing n=1 character term is strictly positive for beta>0,
# and begins at original-source order 121*beta**3/16.
X=s.symbols('X',positive=True)
def al(n,x):return 2*(n+1)*s.besseli(n+1,x)/x
term1=al(1,11*X)**2*al(1,X)/2
assert s.limit(term1/X**3,X,0)==s.Rational(121,16)
checks['symbolic']+=1
assert s.simplify(s.diff(al(0,X),X)-al(1,X)/2)==0
checks['symbolic']+=1

mp.mp.dps=65
for be in (mp.mpf('0.1'),mp.mpf('0.3'),mp.mpf('1'),mp.mpf('3')):
 a,b,c=11*be,11*be,be
 ana=lambda n,x:2*(n+1)*mp.besseli(n+1,x)/x
 terms=[ana(n,a)*ana(n,b)*ana(n,c)/(n+1) for n in range(31)]
 assert all(v>0 for v in terms)
 full=mp.exp(-23*be)*sum(terms)
 independent=mp.exp(-23*be)*terms[0]
 assert full>independent>0
 # All n>20 omitted have a rigorous absolutely convergent positive tail;
 # the displayed truncated value is only a numerical sanity check.
 assert sum(terms[21:])<mp.mpf('1e-13')*sum(terms)
 checks['tail']+=4

# General pointwise sum tail for x=beta/2, a=b=11beta,c=beta:
#   R_K <= exp(-beta+beta^2/4) sum_{n>K}(n+1)(beta/2)^n/n!
# because a_n(x)<= (n+1) exp(x) and a_n(x)<=exp(x^2/4)(x/2)^n/n!.
for beta in [Q(1,100),Q(1,4),Q(1,2),Q(1),Q(3)]:
 for K in [5,10,15]:
  x=beta/2
  rat=x*Q(K+3,(K+2)**2)
  assert rat<1
  tail_first=Q(K+2)*x**(K+1)/factorial(K+1)
  geometric_upper=tail_first/(1-rat)
  exact_prefix=sum(((n+1)*x**n/factorial(n) for n in range(K+1,100)),Q(0))
  assert exact_prefix<=geometric_upper
  checks['tail']+=3

print('PASS SymPy',s.__version__,sum(checks.values()),'exact assertion groups',checks)
print('FULL ORIGINAL L4: SU2 1024 links, 1536 faces, 2 genuine adjacent F19 pairs, 1513 untouched faces')
print('S(V,W)=23-11*t(V)-11*t(W)-t(V^-1 W), all original other links I')
print('EXACT CONTINUOUS SU2^2 Haar joint T=exp(-23 beta) sum_n a_n(11beta)^2 a_n(beta)/(n+1)')
print('a_n(x)=2(n+1)*BesselI(n+1,x)/x, strict interaction term n1~121 beta^3/16')
print('Original shared fine mark F=1-t(V^-1W), marked mass = T-(d/dc)T with a,b fixed')
print('OPEN full 960-variable Haar, physical CMP119 Eq171 constrained T/FP/E/R/B/V, W3, OS')
