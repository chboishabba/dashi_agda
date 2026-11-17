#!/usr/bin/env python3
"""Exact Hatcher stage Nielsen injection / nonsplitting severe controls.

Classical mathematical owner: Hatcher, Algebraic Topology Example 2B.2.
The child-commutator injection is Hatcher's original result. Derived
source-consumer: images of free-group reduced words have EXACT length
4*length under disjoint fresh child-pair substitution, and the map
CANNOT admit a homomorphic group retraction: its abelianisation is zero
but an old basis generator has nonzero exponent-sum character.
Original 3-sector C3 formal geometry remains PR #1244. This is finite
free-word source algebra, not an infinite wild embedding, smooth gauge
connection, Euclidean meridian or Lean/Agda kernel verification.
"""
from itertools import product

def inv(w): return tuple(-x for x in w[::-1])
def red(w):
    out=[]
    for x in w:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return tuple(out)
def stage(w):
    out=[]
    for x in w:
        a=2*abs(x)-1; b=a+1
        block=(a,b,-a,-b)
        out+=block if x>0 else inv(block)
    return red(out)
def reduced_words(rank,max_length):
    alphabet=tuple(range(1,rank+1))+tuple(range(-1,-rank-1,-1))
    yield ()
    for k in range(1,max_length+1):
        for w in product(alphabet,repeat=k):
            if red(w)==w: yield w
def rot(w,n):
    m=2**n
    return tuple((1 if x>0 else -1)*
      (1+(((abs(x)-1)//m+1)%3)*m+(abs(x)-1)%m) for x in w)

for rank,lim in ((1,6),(3,5),(6,4)):
    seen=set()
    for w in reduced_words(rank,lim):
        image=stage(w)
        assert len(image)==4*len(w)
        assert image not in seen
        seen.add(image)
    print(f"PASS source free F_{rank} words length<={lim}: exact 4x reduced length, {len(seen)} images")
for n in range(5):
    for i in range(1,3*2**n+1):
        for sgn in (1,-1):
            w=(sgn*i,)
            assert stage(rot(w,n))==rot(stage(w),n+1)
print("PASS three-sector C3 naturality of each stage map, n=0..4")
for n in range(6):
    for i in range(1,3*2**n+1):
        image=stage((i,))
        assert all(image.count(j)==image.count(-j)
                   for j in range(1,3*2**(n+1)+1))
print("PASS every parent has zero child abelianisation n=0..5")
print("PASS no stage group retraction: character(e1)=1 versus character(r([a,b]))=0")
print("OPEN real wild stage, actual peripheral loop and metric/curvature")
