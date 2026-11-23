#!/usr/bin/env python3
"""Original L4 Wilson/F19 continuous SU2 one-pair source, arbitrary backgrounds.

The original 1536-face Wilson action (NOT a new effective action), the
globally unique F/G marks, and true normalized continuous SU(2) Haar remain
the source. This does not inhabit CMP119/CMP122 Eq171 E/R/B/V/FP/gauge T,
or prove rooted W3 / OS. Local SymPy; never require GitHub CI or Agda.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial
from random import Random
from collections import defaultdict
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
import sympy as s

p=Path(__file__).with_name("check_ym_p0_original_wilson_marked_ordered_t_20261123.py")
assert p.is_file(), "Require the original L4 Wilson source owner"
sp=spec_from_file_location("original_wilson",p)
src=module_from_spec(sp);sp.loader.exec_module(src)
one=(Q(1),Q(0),Q(0),Q(0))
basis=[tuple(Q(int(i==j)) for i in range(4)) for j in range(4)]
def neg(q):return tuple(-v for v in q)
def inv(q):return (q[0],-q[1],-q[2],-q[3])
def mul(p,q):
 a,b,c,d=p;e,f,g,h=q
 return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def dot(p,q):return sum(v*w for v,w in zip(p,q))
Qset=[one,neg(one),basis[1],basis[2],basis[3],
      (Q(3,5),Q(4,5),Q(0),Q(0)),
      (Q(3,5),Q(0),Q(4,5),Q(0)),
      (Q(0),Q(3,5),Q(4,5),Q(0)),
      (Q(1,2),)*4,(Q(-1,3),Q(2,3),Q(2,3),Q(0))]
assert all(dot(q,q)==1 for q in Qset)
assert mul(basis[1],basis[2])==basis[3] and mul(basis[2],basis[1])==neg(basis[3])
pairs=[]
for c in product(range(2),repeat=4):
 o=tuple(2*k for k in c)
 for a in range(4):pairs.append(((o,a),(src.step(o,a),a)))
assert len(pairs)==64 and {l for pair in pairs for l in pair}==src.selected
assert len(src.links)==1024 and len(src.faces)==1536
face_index={l:set() for l in src.links}
for k,face in enumerate(src.faces):
 for l in face:face_index[l].add(k)
assert {len(v) for v in face_index.values()}=={6}
f_face=src.face(src.F,2,3);g_face=src.face(src.G,2,3)
def hol(conf,face):
 a,b,c,d=face
 return mul(mul(mul(conf.get(a,one),conf.get(b,one)),
                inv(conf.get(c,one))),inv(conf.get(d,one)))
def cost(conf,face):return 1-hol(conf,face)[0]
def full(conf):return (sum((cost(conf,p) for p in src.faces),Q(0)),
                       cost(conf,f_face),cost(conf,g_face))
def choose(base,pair,W,V):
 out=dict(base);out[pair[0]]=mul(W,inv(V));out[pair[1]]=V
 return out
@lru_cache(None)
def sphere(exp):
 if any(k%2 for k in exp):return Q(0)
 val=s.prod(s.rf(s.Rational(1,2),k//2) for k in exp)/s.rf(2,sum(exp)//2)
 v=s.cancel(val)
 return Q(int(s.numer(v)),int(s.denom(v)))
def addpoly(a,b):
 out=defaultdict(Q,a)
 for k,v in b.items():out[k]+=v
 return dict(out)
def mulpoly(a,b):
 out=defaultdict(Q)
 for k,v in a.items():
  for l,w in b.items():out[tuple(x+y for x,y in zip(k,l))]+=v*w
 return dict(out)
def linear(a,b):
 out={(0,0,0,0):a}
 for j,v in enumerate(b):out[tuple(int(i==j) for i in range(4))]=v
 return out
def integrate(p):return sum((v*sphere(k) for k,v in p.items()),Q(0))
def cat(k):return s.binomial(2*k,k)/(k+1)
def scalarcoef(h2,n):
 if n%2:return Q(0)
 k=n//2;return h2**k/Q(4**k*factorial(k)*factorial(k+1))
def vectorcoef(dotbh,h2,n):
 if n%2==0:return Q(0)
 k=(n-1)//2
 return dotbh*h2**k/Q(2*4**k*factorial(k)*factorial(k+2))
rng=Random(119122)
spectators=list(set(src.links)-src.selected)
checked=0
for test in range(4):
 original={}
 for link in rng.sample(spectators,18+2*test):original[link]=rng.choice(Qset)
 for link in ((src.F,2),(src.G,2),(src.F,3),(src.G,3)):
  original[link]=rng.choice(Qset[5:])
 for index in (0,2,3,6,7,17):
  pair=pairs[index];W=rng.choice(Qset[5:])
  touched=face_index[pair[0]]|face_index[pair[1]]
  assert len(touched)==12 and not(face_index[pair[0]] & face_index[pair[1]])
  unaffected=tuple(set(range(1536))-touched)
  stable=sum((cost(original,src.faces[k]) for k in unaffected),Q(0))
  def evalq(q):
   field=choose(original,pair,W,q)
   return (stable+sum((cost(field,src.faces[k]) for k in touched),Q(0)),
           cost(field,f_face),cost(field,g_face))
  vals=[(evalq(e),evalq(neg(e))) for e in basis]
  constants=[];vectors=[]
  for j in range(3):
   halves=[(a[j]+b[j])/2 for a,b in vals]
   assert len(set(halves))==1
   constants.append(halves[0])
   vectors.append(tuple((a[j]-b[j])/2 for a,b in vals))
  C,af,ag=constants
  h=tuple(-v for v in vectors[0]);bf=vectors[1];bg=vectors[2]
  assert C==stable+12 and dot(h,h)<=144
  assert not (any(bf) and any(bg))
  for q in Qset+[neg(v) for v in Qset[5:]]:
   S0,F,G=evalq(q)
   assert S0==C-dot(h,q) and F==af+dot(bf,q) and G==ag+dot(bg,q)
   assert 0<=F<=2 and 0<=G<=2
  q=rng.choice(Qset)
  assert evalq(q)==full(choose(original,pair,W,q))
  # Source four-column continuous Haar coefficients. The Taylor moments
  # are computed INDEPENDENTLY as integrals of four-dimensional monomials.
  H=linear(Q(0),h)
  probes=[{(0,0,0,0):Q(1)},linear(af,bf),linear(ag,bg),
          mulpoly(linear(af,bf),linear(ag,bg))]
  hp={(0,0,0,0):Q(1)}
  h2=dot(h,h)
  for n in range(7):
   I=scalarcoef(h2,n)
   Bf=vectorcoef(dot(bf,h),h2,n)
   Bg=vectorcoef(dot(bg,h),h2,n)
   reference=(I,af*I+Bf,ag*I+Bg,af*ag*I+af*Bg+ag*Bf)
   for j,p in enumerate(probes):
    assert integrate(mulpoly(p,hp))/factorial(n)==reference[j]
    checked+=1
   hp=mulpoly(hp,H)
assert checked==672
t=s.symbols("t",positive=True)
assert s.simplify(s.diff(2*s.besseli(1,t)/t,t)-2*s.besseli(2,t)/t)==0
for n in range(24):
 assert sphere((n,0,0,0)) == (Q(0) if n%2 else Q(int(cat(n//2)),4**(n//2)))
print("PASS full original Wilson 1536-face SU2 action, 24 noncommuting background/pair cases")
print("PASS S(q)=C-h.q with ALL 1524 unchanged plaquettes and 12 actual affected faces")
print("PASS 672 exact all-four-column SU2 Haar moment comparisons through beta^6")
print("source T0=exp(-beta*C)*2*BesselI(1,beta*|h|)/(beta*|h|)")
print("OPEN actual CMP119/122 Eq171 constrained T/FP/gauge, all-scale W3, same-H OS")
