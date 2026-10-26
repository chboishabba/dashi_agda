#!/usr/bin/env python3
"""Exact continuous piecewise-linear 3-strand bridge on the balanced 3x3 sheet.
Coordinates are (x,y), not state counts. Each interpolated edge is affine
over rational u in [0,1]. Proves six-step mirror and four-step C3 covariance
for all real u (affine identity), and checks exact pairwise noncollision.
"""
from fractions import Fraction as Q
from itertools import combinations
P=((-1,1),(0,1),(0,0),(0,-1),(1,-1),(1,0),
   (1,1),(0,1),(0,0),(0,-1),(-1,-1),(-1,0))
def point(k,j,u):
    p=P[(k+4*j)%12];q=P[(k+4*j+1)%12]
    return tuple(Q(v)+u*Q(w-v) for v,w in zip(p,q))
def mirror(p):return (-p[0],p[1])
# Affine function equality is determined by its values at u=0 and 1.
for k in range(12):
    for j in range(3):
        for u in (Q(0),Q(1)):
            assert point(k+6,j,u)==mirror(point(k,j,u))
            assert point(k+4,j,u)==point(k,(j+1)%3,u)
# For each pair and segment, a collision requires simultaneously
# dx(u)=0 and dy(u)=0. If a coordinate has nonzero slope, it determines
# the sole candidate rational root; otherwise it is either always zero
# or never zero.
def roots(a,b):
    if a==b==0:return None  # identically zero
    if b==0:return []       # never zero
    return [-a/b] if Q(0)<=-a/b<=Q(1) else []
margin=None
for k in range(12):
    for i,j in combinations(range(3),2):
        d0=tuple(point(k,i,Q(0))[t]-point(k,j,Q(0))[t] for t in range(2))
        d1=tuple(point(k,i,Q(1))[t]-point(k,j,Q(1))[t] for t in range(2))
        r=[roots(d0[t],d1[t]-d0[t]) for t in range(2)]
        collision=(r[0] is None and r[1] is None) or (
          r[0] is None and r[1]!=[]) or (
          r[1] is None and r[0]!=[]) or (
          r[0] is not None and r[1] is not None and any(x==y for x in r[0] for y in r[1]))
        assert not collision,(k,i,j,d0,d1,r)
        # Minimum norm² of affine difference is at endpoint or vertex.
        da=tuple(d1[t]-d0[t] for t in range(2))
        norm=lambda z:sum((d0[t]+z*da[t])**2 for t in range(2))
        denom=sum(v*v for v in da)
        uv=max(Q(0),min(Q(1),-sum(d0[t]*da[t] for t in range(2))/denom)) if denom else Q(0)
        m=norm(uv)
        margin=m if margin is None else min(margin,m)
assert margin>0
print('PASS piecewise-affine 3-strand six-step mirror for all real interpolation parameters')
print('PASS four-step cyclic C3 covariance; exact no-collision on 36 pair-edge tests')
print('EXACT minimum squared strand separation:',margin)
print('LIMIT: no proof of framing normal or braid isotopy in 3D; this is a PL planar-motion receipt')
