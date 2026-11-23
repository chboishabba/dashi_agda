#!/usr/bin/env python3
"""Original Wilson L4 bond/face C3, time-mirror and 18-neighbour influence graph.

One original geometry; not a full continuous SU(N) Gibbs/RP/OS or W3 proof.
The two routes are geometrically equivariant, not equal to a TOE Hamiltonian.
"""
from itertools import combinations,product
from collections import defaultdict
from fractions import Fraction as Q
L=4
sites=list(product(range(L),repeat=4))
links=[(x,i) for x in sites for i in range(4)]
link_set=set(links)
def shift(x,i,step=1):
    y=list(x);y[i]=(y[i]+step)%L;return tuple(y)
def face(x,i,j):
    return frozenset(((x,i),(shift(x,i),j),(shift(x,j),i),(x,j)))
plaquettes={face(x,i,j) for x in sites for i,j in combinations(range(4),2)}
assert len(links)==1024 and len(plaquettes)==1536

def c_site(x):return (x[0],x[3],x[1],x[2]) # x1->x2, x2->x3, x3->x1
rot={0:0,1:2,2:3,3:1}
def c_link(b):x,i=b;return (c_site(x),rot[i])
def t_site(x):return ((-x[0])%L,x[1],x[2],x[3])
def t_link(b):
    x,i=b
    return (shift(t_site(x),0,-1),0) if i==0 else (t_site(x),i)
def mp_face(p,fn):return frozenset(fn(b) for b in p)
for fn in (c_link,t_link):
    assert {fn(b) for b in links}==link_set
    assert {mp_face(p,fn) for p in plaquettes}==plaquettes
    for p in plaquettes:assert mp_face(p,fn) in plaquettes
for b in links:
    assert c_link(c_link(c_link(b)))==b
    assert t_link(t_link(b))==b
    assert c_link(t_link(b))==t_link(c_link(b))
neighbors=defaultdict(set)
for p in plaquettes:
    assert len(p)==4
    for a in p:
        neighbors[a]|=(p-{a})
assert all(len(neighbors[b])==18 for b in links)
for fn in (c_link,t_link):
    for a in links:
        assert {fn(b) for b in neighbors[a]}==neighbors[fn(a)]
assert sum(len(neighbors[b]) for b in links)==18432
# Real beta in the lattice high-temp domain; exactly rational sufficient bound
# beta <= 1/36, q <= 18 beta <= 1/2, preserved by all source automorphisms.
beta=Q(1,36); q=Q(18)*beta
assert q==Q(1,2)
# Show observed support distances are exactly preserved by C3 and time mirror.
def distance(A,B):
    frontier=set(A); seen=set(A);d=0
    while frontier:
        if frontier&B:return d
        nxt={c for b in frontier for c in neighbors[b]}-seen
        seen|=nxt;frontier=nxt;d+=1
    raise AssertionError('disconnected')
orig=face((0,0,0,0),1,2)
far=face((0,0,0,2),1,2)
assert not orig & far
r=distance(orig,far)
for fn in (c_link,t_link,lambda x:c_link(t_link(x))):
    assert distance({fn(b) for b in orig},{fn(b) for b in far})==r
# C3 equality of link graph adjacency and Wilson plaquette supports is exact.
# Reflection maps time links to inverted holonomies. Support invariance does NOT
# by itself establish Wilson positivity, source physical RP or a same-H gap.
print('PASS 1024 original Wilson links, 1536 plaquette supports, 18 neighbours/link')
print('PASS full C3 action order three, time mirror order two, and commuting square on 1024 links')
print('PASS plaquette support set preserved by C3 and time mirror (1536 each)')
print('PASS entire 18432 directed Dobrushin neighbour incidences equivariant')
print('PASS original support distance preserved:',r)
print('PASS beta<=1/36, q<=1/2 original sufficient strong-coupling bound is C3/mirror-equivariant')
print('NOT PROVED: full continuous SUN reflection positivity, positive-time observables, UV beta(a), physical CMP119/122 W3, or TOE H equality')
