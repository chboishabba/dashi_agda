#!/usr/bin/env python3
"""Original L4 Wilson/F19 side-two anchored axial-Haar and Dirichlet gauge test.

Original 1024 native links / 1536 plaquettes, 16 interior site gauges,
one boundary anchor plus 15 interior tree edges. This is a finite regression
of a general compact-Haar analytic theorem, NOT a replacement SU(N) Q8 Haar
measure, and NOT physical Balaban CMP122 rT/Q_B/FP/ghost/R or W3/Clay.
"""
from collections import deque, Counter
from itertools import product, combinations
from fractions import Fraction as Q
from math import comb
from random import Random
import sympy as s
L=4
sites=list(product(range(L),repeat=4))
def step(x,a):
 y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
links=[(x,a) for x in sites for a in range(4)]
faces=[((x,a),(step(x,a),b),(step(x,b),a),(x,b))
       for x in sites for a,b in combinations(range(4),2)]
B=set(product(range(2),repeat=4))
anchor=((1,0,0,0),0)
root=anchor[0];external=step(*anchor)
internal=[e for e in links if e[0] in B and step(*e) in B]
crossing=[e for e in links if (e[0] in B)!=(step(*e) in B)]
assert (len(sites),len(links),len(faces),len(B),len(internal),len(crossing))==(256,1024,1536,16,32,64)
adj={x:[] for x in B}
for e in internal:
 x,a=e;y=step(*e);adj[x].append((y,e,1));adj[y].append((x,e,-1))
order=[root];parents={root:None};todo=deque([root])
while todo:
 x=todo.popleft()
 for y,e,sgn in adj[x]:
  if y not in parents:
   parents[y]=(x,e,sgn);order.append(y);todo.append(y)
forest=[anchor]+[parents[x][1] for x in order[1:]]
assert len(order)==len(forest)==16 and len(set(forest))==16
one=(1,0,0,0)
Q8=tuple(tuple(sign*int(i==j) for i in range(4)) for j in range(4) for sign in (1,-1))
def mul(p,q):
 a,b,c,d=p;e,f,g,h=q
 return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def inv(x):return(x[0],-x[1],-x[2],-x[3])
def prod(*xs):
 a=one
 for x in xs:a=mul(a,x)
 return a
def gauge(U,g):
 return {e:prod(g.get(e[0],one),U[e],inv(g.get(step(*e),one))) for e in links}
def fixed(U):
 g={root:inv(U[anchor])}
 for x in order[1:]:
  parent,e,sign=parents[x]
  g[x]=mul(g[parent],U[e] if sign==1 else inv(U[e]))
 X=gauge(U,g)
 assert all(X[e]==one for e in forest)
 return X
def hol(U,p):
 a,b,c,d=p;return prod(U[a],U[b],inv(U[c]),inv(U[d]))
def deficit(U,p):return 1-hol(U,p)[0]
def face(x,a,b):return ((x,a),(step(x,a),b),(step(x,b),a),(x,b))
F=face((0,0,0,0),2,3);G=face((0,0,0,2),2,3)
assert F in faces and G in faces
def original(U):
 return (sum(deficit(U,p) for p in faces),deficit(U,F),deficit(U,G))
counts=Counter()
rng=Random(119122445)
for trial in range(4):
 U={e:one for e in links}
 for e in rng.sample(links,120+trial*10):U[e]=rng.choice(Q8)
 X=fixed(U)
 assert original(X)==original(U)
 h={x:rng.choice(Q8) for x in B}
 X2=fixed(gauge(U,h))
 assert X2==X
 counts['original_gauge']+=2
 Ug=gauge(U,h)
 for p in faces:
  at=p[0][0]
  assert hol(Ug,p)==prod(h.get(at,one),hol(U,p),inv(h.get(at,one)))
  counts['native_plaquettes']+=1
 for c in product(range(2),repeat=4):
  x=tuple(2*i for i in c)
  for a in range(4):
   e0=(x,a);e1=(step(x,a),a);y=step(*e1)
   assert prod(Ug[e0],Ug[e1])==prod(h.get(x,one),prod(U[e0],U[e1]),inv(h.get(y,one)))
   counts['native_R445']+=1
# Real block standard Landau, NOT Balaban's selected axial/background gauge.
A=s.zeros(16);idx={x:i for i,x in enumerate(sorted(B))}
for x,a in internal:
 i=idx[x];j=idx[step(x,a)];A[i,j]+=1;A[j,i]+=1
D=8*s.eye(16)-A;K=8*s.eye(16)+A
assert D.eigenvals()=={s.Integer(4):1,s.Integer(6):4,s.Integer(8):6,s.Integer(10):4,s.Integer(12):1}
assert K.eigenvals()=={s.Integer(12):1,s.Integer(10):4,s.Integer(8):6,s.Integer(6):4,s.Integer(4):1}
assert D.det()==s.prod((4+2*j)**comb(4,j) for j in range(5))
counts['local_Dirichlet']+=3
for bits in product((0,1),repeat=4):
 v=s.Matrix([(-1)**sum(bits[i]*x[i] for i in range(4)) for x in sorted(B)])
 assert D*v==(4+2*sum(bits))*v
 counts['local_Dirichlet']+=1
for b in range(1,9):
 t=s.pi/(b+1)
 assert s.simplify(s.trigsimp((1-s.cos(t))/(1+s.cos(t))-s.tan(t/2)**2,method='fu'))==0
 counts['scale_radius']+=1
assert s.simplify((1-s.cos(s.pi/3))/(1+s.cos(s.pi/3)))==s.Rational(1,3)
counts['scale_radius']+=1
# A noninvariant OPEN original tree-link trace is not equal after removing
# its gauge orbit: continuous SU(N) Haar first moment is 0; fixed tree value 1.
assert sum(q[0] for q in Q8)==0 and one[0]==1
counts['open_link_nogo']+=1
# Check the 2^4 coordinate reflections and 4! permutations mentioned in
# Balaban CMP122 Eq.(1.71) as 384 frames of OUR candidate axial tree.
# This is NOT a proof that the candidate graph equals his source-selected rT.
from itertools import permutations
def transform_frame_point(x,perm,flips):
 return tuple((1-x[perm[i]] if flips[i] else x[perm[i]])%L for i in range(4))
def oriented_native_edge(x,y):
 for a in range(4):
  if step(x,a)==y:return (x,a),1
  if step(y,a)==x:return (y,a),-1
 raise AssertionError((x,y))
original_config={e:one for e in links}
for e in rng.sample(links,130):original_config[e]=rng.choice(Q8)
original_moments=original(original_config)
all_frames=set()
for perm in permutations(range(4)):
 for flips in product((0,1),repeat=4):
  r=transform_frame_point(root,perm,flips)
  ext=transform_frame_point(external,perm,flips)
  anchor_edge,sgn=oriented_native_edge(r,ext)
  h={r:inv(original_config[anchor_edge]) if sgn==1 else original_config[anchor_edge]}
  selected=[anchor_edge]
  for child in order[1:]:
   p,e,oldsign=parents[child]
   x=transform_frame_point(p,perm,flips)
   y=transform_frame_point(child,perm,flips)
   ref,sign=oriented_native_edge(x,y)
   h[y]=mul(h[x],original_config[ref] if sign==1 else inv(original_config[ref]))
   selected.append(ref)
  assert len(set(selected))==16 and set(h)==B and ext not in h
  frame=tuple(sorted(selected))
  assert frame not in all_frames
  all_frames.add(frame)
  X=gauge(original_config,h)
  assert all(X[e]==one for e in selected)
  assert original(X)==original_moments
  counts['source_rotated_candidate_frame']+=1
assert len(all_frames)==384
counts['source_rotated_candidate_frame']+=1

print('PASS',s.__version__,sum(counts.values()),dict(counts))
print('Original full L4 Wilson action/marks: exactly 16 anchored tree links -> 1008 remaining')
print('Standard Dirichlet Landau local sufficient radius delta < 1/3, NOT CMP122 background FP')
print('OPEN CMP119/122 selected rT,Q_B,R, normalized two-mark W3, same-H OS and Clay mass gap')
