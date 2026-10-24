#!/usr/bin/env python3
"""Exact overlap: Griess SL3(3) source lines vs original Agda open P3^3.

Original mathematical roots:
R. L. Griess Jr., J. Algebra 131 (1990) 281–293 (F3^3 normalizer);
DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact (the
already existing BALANCED grid -1 <-> 0 <-> +1, no +/- wraparound);
IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact (13 atom,
separate arithmetic identity), no imaginary graph->Albert action.

This script enumerates ALL invertible matrices GL3(3), not just a
preferred subgroup. It does not silently map 0,1,2 to a wrong open
path: nonzero 1/2 are BOTH adjacent to balanced zero, but NOT each other.
"""
from itertools import product,combinations
from collections import Counter
V=tuple(product(range(3),repeat=3))
origin=(0,0,0)
neg=lambda a:tuple((-x)%3 for x in a)
projective=tuple(v for v in V if v!=origin and v<neg(v))
assert len(projective)==13
axes=((1,0,0),(0,1,0),(0,0,1))
def det(M):
 a,b,c=M
 return (a[0]*(b[1]*c[2]-b[2]*c[1])
        -a[1]*(b[0]*c[2]-b[2]*c[0])
        +a[2]*(b[0]*c[1]-b[1]*c[0]))%3
def apply(M,v):
 return tuple(sum(M[i][j]*v[j] for j in range(3))%3 for i in range(3))
edges=set()
for v in V:
 for i in range(3):
  if v[i] in (1,2):
   u=list(v);u[i]=0
   edges.add(frozenset((v,tuple(u))))
assert len(edges)==54
line=lambda v:frozenset((v,neg(v)))
triangle={line(v) for v in axes}
counts=Counter();cube=[];triangleStabilizer=[]
for M in product(V,repeat=3):
 d=det(M)
 if d==0:continue
 counts[d]+=1
 if {line(apply(M,v)) for v in axes}==triangle:
  triangleStabilizer.append(M)
 if all(frozenset(apply(M,v) for v in e) in edges for e in edges):
  cube.append(M)
assert counts=={1:5616,2:5616}
assert len(cube)==len(triangleStabilizer)==48
assert set(cube)==set(triangleStabilizer)
assert sum(det(M)==1 for M in cube)==24
images=set()
for M in cube:
 images.add(tuple(next(j for j,b in enumerate(projective)
  if line(b)==line(apply(M,v))) for v in projective))
assert len(images)==24 # global inversion is kernel of projectivization
assert 5616//24==234
print('PASS GL3(3)=11232, SL3(3)=5616')
print('PASS precisely 48 invertible linear source actions preserve original open cube adjacency')
print('PASS cube actions equal the projective coordinate-triangle stabilizer')
print('PASS SL3 intersection=24, effective PG(2,3) image=24, index234')
print('STOP: no full Griess source normalizer action preserves open P3^3; no Monster/physical inference')
