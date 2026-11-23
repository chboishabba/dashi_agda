#!/usr/bin/env python3
"""Exact minimum five new exterior plaquettes for original L4 F/G 2-step tube.

Fix original marked F/G caps and allow arbitrary deletion of the eight T
walls; find square-free external support S that cancels native link parity
outside the original capped tube. All connected exterior families up to
four faces touching the tube are exhaustively enumerated using original
external-link overlap. Does NOT exclude repeated face insertions, non-Z2
representation channels, other starting connecting surfaces or full W3.
"""
from itertools import combinations, product
from collections import Counter, defaultdict
L=4
sites=tuple(product(range(L),repeat=4))
def step(x,a):
    y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
def word(x,a,b):
    return ((x,a,1),(step(x,a),b,1),(step(x,b),a,-1),(x,b,-1))
P={(x,a,b):word(x,a,b) for x in sites for a,b in combinations(range(4),2)}
links=sorted((x,a) for x in sites for a in range(4))
li={e:i for i,e in enumerate(links)}
assert (len(sites),len(links),len(P))==(256,1024,1536)
def boundary(p):
    result=0
    for x,a,_ in P[p]: result^=1<<li[(x,a)]
    return result
bits={p:boundary(p) for p in P}
F=((0,0,0,0),1,2)
G=((2,0,0,0),1,2)
H=((1,0,0,0),1,2)
T=frozenset(((t,y,z,0),0,a)
            for t in range(2) for a in (1,2)
            for y,z in ([(0,0),(0,1)] if a==1 else [(0,0),(1,0)]))
assert len(T)==8
inside=0
for p in (F,G,*T): inside|=bits[p]
assert inside.bit_count()==20
outside_mask=((1<<1024)-1)^inside
E=sorted(set(P)-set(T)-{F,G,H})
assert len(E)==1525
external_bits=[bits[p]&outside_mask for p in E]
assert Counter(z.bit_count() for z in external_bits)==Counter({3:76,4:1449})
incidence=defaultdict(list)
for i,p in enumerate(E):
    for x,a,_ in P[p]:
        j=li[(x,a)]
        if not ((inside>>j)&1): incidence[j].append(i)
adj=[set() for _ in E]
for members in incidence.values():
    for i in members: adj[i].update(members)
for i in range(len(E)): adj[i].discard(i)
roots=[i for i,p in enumerate(E) if bits[p]&inside]
assert len(roots)==76
frontier={frozenset((i,)) for i in roots}
expected=[76,992,18314,388968]
total=0
for size in range(1,5):
    assert len(frontier)==expected[size-1],(size,len(frontier))
    for family in frontier:
        parity=0
        for i in family:parity^=external_bits[i]
        assert parity!=0,('unexpected outside-link closure',size,family)
    total+=len(frontier)
    print('PASS size %d: %d connected rooted external subsets; zero outside boundary 0'%(size,len(frontier)))
    if size==4:break
    next_frontier=set()
    for family in frontier:
        neighbors=set()
        for i in family:neighbors.update(adj[i])
        for j in neighbors.difference(family):
            next_frontier.add(family|{j})
    frontier=next_frontier
assert total==408350
# Any external set with overall zero exterior boundary splits into components
# under shared external-link incidence. Its components have disjoint exterior
# link sets, hence each component must separately have zero outside boundary.
# A component with no tube-root cannot cancel the F/G tube itself. The above
# exhausts every tube-rooted component of size <=4.
def cube(x,axes):
    a,b,c=axes
    return frozenset(((x,a,b),(step(x,c),a,b),(x,a,c),
                      (step(x,b),a,c),(x,b,c),(step(x,a),b,c)))
cubes={cube(x,axes) for x in sites for axes in combinations(range(4),3)}
flips=[c for c in cubes if len(c&T)==1 and F not in c and G not in c]
assert len(flips)==24
new_sets=set()
for c in flips:
    external=c-T
    assert len(external)==5 and external<=set(E)
    parity=0
    for p in external:parity^=bits[p]
    assert parity & outside_mask==0
    removed=next(iter(c&T))
    assert parity==bits[removed]
    new=frozenset((set(T)-{removed})|external)
    assert len(new)==12
    full=bits[F]^bits[G]
    for p in new:full^=bits[p]
    assert full==0
    new_sets.add(new)
assert len(new_sets)==24
print('PASS 24 distinct size-five cube-boundary exterior witnesses and F/G closures')
print('RESULT minimal external count = 5 for square-free parity-closed changes to this original T')
print('OPEN repeated interactions, alternate original paths, all-coupling CMP119/W3/OS')
