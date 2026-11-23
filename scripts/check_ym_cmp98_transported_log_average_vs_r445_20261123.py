#!/usr/bin/env python3
"""Exact abelian SU(2) maximal-torus example of CMP98 Eq.(15)-style average.

The 16 offset root paths are a selected explicit axial contour convention.
This is not a formal identification of the paper's full gauge/chart convention
or a source proof for arbitrary nonabelian SU(N).
"""
from fractions import Fraction as F
from itertools import product
import sympy as sp

origin=(0,0,0,0)
axis=0
finish=(2,0,0,0)
offsets=list(product(range(2),repeat=4))
assert len(offsets)==16

def move(site,j):
    site=list(site)
    site[j]+=1
    return tuple(site)
def plus(x,y):return tuple(a+b for a,b in zip(x,y))
def rooted(root, offset):
    here=root
    edges=[]
    for j in range(4):
        for _ in range(offset[j]):
            edges.append((here,j))
            here=move(here,j)
    assert here==plus(root,offset)
    return edges

def path_segments(offset):
    x=plus(origin,offset)
    a=rooted(origin,offset)
    middle=[(x,axis),(move(x,axis),axis)]
    tail=list(reversed(rooted(finish,offset)))
    return a,middle,tail

# One phase on a positive link, other 1023 links identity.
active=((0,1,0,0),0)
theta=F(1,8)  # link is diag(e^{i*pi/8},e^{-i*pi/8}) in SU(2)
def link_angle(bond):return theta if bond==active else F(0)
def walk_angle(offset):
    start,middle,end=path_segments(offset)
    return sum((link_angle(b) for b in start+middle),F(0))-sum((link_angle(b) for b in end),F(0))

native=link_angle((origin,0))+link_angle(((1,0,0,0),0))
contours=[walk_angle(offset) for offset in offsets]
relative=[phase-native for phase in contours]
assert native==0
assert relative.count(theta)==1 and relative.count(0)==15
assert all(abs(x)<1 for x in relative)  # principal log branch
average_phase=native+sum(relative,F(0))/len(offsets)
assert average_phase==F(1,128)
assert average_phase!=native
Q=sp.exp(sp.I*sp.pi*sp.Rational(average_phase.numerator,average_phase.denominator))
W=sp.Integer(1)
assert sp.simplify(Q-sp.exp(sp.I*sp.pi/128))==0
assert sp.simplify(Q-W)!=0

# Exact gauge transformation: all path endpoints are the same.
def gauge(site):return F(sum((i+1)*v for i,v in enumerate(site)),512)
def gauge_link(bond):
    s,j=bond
    return link_angle(bond)+gauge(s)-gauge(move(s,j))
def gauge_walk(offset):
    start,middle,end=path_segments(offset)
    return sum((gauge_link(b) for b in start+middle),F(0))-sum((gauge_link(b) for b in end),F(0))
expected=gauge(origin)-gauge(finish)
assert all(gauge_walk(x)==walk_angle(x)+expected for x in offsets)
assert (native+expected)+sum((gauge_walk(x)-(native+expected) for x in offsets),F(0))/16==average_phase+expected
print('PASS: explicit 16 transported contours / 4D block, principal logarithm branch')
print('PASS: straight native R445 W = 1, selected nonlinear contour average Q = exp(i*pi/128)')
print('PASS: 16/16 source-endpoint gauge covariance; relative contour logs unchanged')
print('LIMIT: axial contour convention example, abelian SU(2) subgroup; not physical all-scale Bałaban T or full SU(N) theorem')
