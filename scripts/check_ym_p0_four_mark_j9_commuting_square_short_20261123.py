#!/usr/bin/env python3
"""Original 4D Wilson Z2-centre restricted 10-link source; 4-mark F19 square.
Finite 9+1 / 5x2 / j observer residual and Singer signed chart checks.
Not full SU(N) Haar, physical time evolution, CMP119 or W3/OS.
"""
from itertools import product, combinations
from fractions import Fraction as Q
import sympy as s
from functools import lru_cache
L=4
sites=list(product(range(L),repeat=4))
def step(x,a):
 y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
def face(x,a,b):return ((x,a),(step(x,a),b),(step(x,b),a),(x,b))
faces=[face(x,a,b) for x in sites for a,b in combinations(range(4),2)]
F=(0,0,0,0);H=(0,0,0,2)
active=((F,2),(step(F,2),2),(H,2),(step(H,2),2))+tuple(
 [((0,0,0,z),2) for z in (1,3)]+[((0,0,1,z),3) for z in range(4)])
assert len(sites)==256 and len(faces)==1536 and len(set(active))==10
ix={b:i for i,b in enumerate(active)}
def mask(bs):
 m=0
 for b in bs:
  if b in ix:m^=1<<ix[b]
 return m
pm=[mask(f) for f in faces];fm=mask(face(F,2,3));gm=mask(face(H,2,3))
coarse=[(tuple(2*z for z in c),a) for c in product(range(2),repeat=4) for a in range(4)]
assert len(coarse)==64 and len({b for x,a in coarse for b in ((x,a),(step(x,a),a))})==128
def moment(bits,n):
 bad=sum((bits&m).bit_count()%2 for m in pm)
 w=Q(1,2)**(n*bad);f=1-2*((bits&fm).bit_count()%2);g=1-2*((bits&gm).bit_count()%2)
 return w,w*f,w*g,w*f*g
def W(bits):return ((bits&1)^((bits>>1)&1),((bits>>2)&1)^((bits>>3)&1))
def field(w,v0,v1,rest):
 return sum(b<<i for i,b in enumerate((w[0]^v0,v0,w[1]^v1,v1,*rest)))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
for n in (1,2,3):
 direct={w:(Q(0),)*4 for w in product((0,1),repeat=2)}
 for bits in range(1024):direct[W(bits)]=add(direct[W(bits)],moment(bits,n))
 for w,actual in direct.items():
  staged=(Q(0),)*4
  for v0,v1 in product((0,1),repeat=2):
   for rest in product((0,1),repeat=6):
    staged=add(staged,moment(field(w,v0,v1,rest),n))
  assert staged==actual
  a,b,c,d=actual;det=a*d-b*c
  assert det!=0
  r=Q(1,4);k00=a;k10=a+r*b;k01=a+r*c;k11=a+r*b+r*c+r*r*d
  assert k11-k10-k01+k00==r*r*d
  assert k11*k00-k10*k01==r*r*det!=0
  for u,v in product((Q(-9,100),Q(0),Q(9,100)),repeat=2):
   z=a+b*u+c*v+d*u*v
   assert z>0 and z*d-(b+d*v)*(c+d*u)==det
 assert len(direct)==4
print('PASS original 1536-plane Wilson 1024 states; 3 coupling slices x 4 coarse fibres x 4 moments')
print('PASS exact F19 ordered/direct, source square, nonzero conditional factorisation defect')
G=s.Matrix([[-1,-1,0],[0,-1,-1],[-1,-1,-1]])
assert (G**13+s.eye(3)).applyfunc(lambda z:int(z)%3)==s.zeros(3)
assert (G**26).applyfunc(lambda z:int(z)%3)==s.eye(3)
@lru_cache(None)
def M(k):return (G**k).applyfunc(lambda z:int(z)%3)
def signed(u):return (-1,0,1,0)[u]
def sd(u):return (int(u)+1)%3-1
@lru_cache(None)
def chart(x,k):
 q=tuple(signed(z) for z in x)+(0,)*5
 return (tuple(sd(v) for i in (0,3,6) for v in M(k)*s.Matrix(q[i:i+3])),
         tuple(None if z%2==0 else (z-1)//2 for z in x))
@lru_cache(None)
def inverse(q,b,k):
 A=M(k).inv_mod(3)
 v=tuple(sd(z) for i in (0,3,6) for z in A*s.Matrix(q[i:i+3]))
 return tuple(0 if z==-1 else 2 if z==1 else 1+2*bb for z,bb in zip(v[:4],b))
for k in range(26):
 assert len({chart(x,k) for x in sites})==256
 assert all(inverse(*chart(x,k),k)==x for x in sites)
 assert len({(chart(x,k),chart(step(x,a),k),x,a) for x in sites for a in range(4)})==1024
print('PASS 26 nonidentity Singer stages: original 256 gauge sites, 1024 native links, zero branch')
pts=list(product((-1,0,1),repeat=2));non=[p for p in pts if p!=(0,0)]
axes={max(p,tuple(-z for z in p)) for p in non};assert len(axes)==4
fibre={(a,orientation):tuple(orientation*z for z in a)
       for a in (sorted(axes)+[(0,0)]) for orientation in (-1,1)}
assert len(fibre)==10 and len(set(fibre.values()))==9
assert sum(p==(0,0) for p in fibre.values())==2
assert len([p for p in non if sum(v==p for v in fibre.values())==1])==8
x,y=s.symbols('x y'); q=x*x-x*y+y*y;v=x*y*(y-x);j=256*q**3/v**2
assert j.subs({x:1,y:2})==j.subs({x:2,y:1})==1728
assert v.subs({x:1,y:2})==-v.subs({x:2,y:1})!=0
assert v.subs({x:1,y:1})==0
assert W(0)==W(3) and moment(0,1)[1]/moment(0,1)[0]!=moment(3,1)[1]/moment(3,1)[0]
print('PASS 5 inversion orbits x two signs -> 9 with double-zero; pointed 9+1 retains zero residual')
print('PASS modular j(1,2)=j(2,1)=1728 yet orientation V opposite; coarse W not F-sufficient')
print('OPEN continuous SU(N) Haar, actual CMP119 T, absolute W3, interacting OS same-H gap')
