#!/usr/bin/env python3
"""Hatcher Z-block marking: once-punctured-torus boundary commutator.

PRIOR MATH: Hatcher Algebraic Topology Example 2B.2 pp 171–172;
once-punctured torus retracts onto wedge of 2 loops with boundary
word [a,b]=a b a^-1 b^-1. Free-group substitution for the horn tower
is already the independent original Agda horn #1244 source owner.

This script checks a combinatorial surface word and length *budgets*,
NOT an embedded Hatcher Z-block, a 3D linked horn, a collar path metric,
or compatible based-meridian representatives on the actual wild exterior.
"""
from fractions import Fraction as Q

def inverse(word):
    return [(name,-s) for name,s in reversed(word)]
def reduced(word):
    stack=[]
    for item in word:
        if stack and stack[-1][0]==item[0] and stack[-1][1]==-item[1]:
            stack.pop()
        else: stack.append(item)
    return stack

def commutator(x,y): return x+y+inverse(x)+inverse(y)

def expansion(prefix,depth):
    if depth==0: return [(prefix,1)]
    a=expansion(prefix+'0',depth-1)
    b=expansion(prefix+'1',depth-1)
    return commutator(a,b)

def abelianization(word):
    z={}
    for name,sign in word: z[name]=z.get(name,0)+sign
    return {name:v for name,v in z.items() if v}

# A punctured-torus square has directed sides a,b,a^-1,b^-1.
boundary=commutator([('a',1)],[('b',1)])
assert boundary==[('a',1),('b',1),('a',-1),('b',-1)]
assert reduced(boundary)==boundary and not abelianization(boundary)
assert abelianization([('a',1)])=={'a':1}
print('PASS punctured-torus boundary has nontrivial reduced [a,b], abelianizes to 0; straight collar has nonzero winding')

for n in range(1,9):
    w=expansion('',n)
    r=reduced(w)
    assert len(w)==4**n and len(r)==len(w)
    assert not abelianization(w)
    assert len(set(a for a,_ in w))==2**n
    # A hypothetical source bound L_leaf(n) <= L0*q^n,
    # with each of 4^n word letters represented by an L_leaf loop,
    # would give L_root <= L0*(4q)^n BEFORE adding stems/clearance.
    q=Q(1,5)
    total=Q(len(w))*(q**n)
    assert total==Q(4,5)**n
    print(f'PASS formal Hatcher commutator-stage n={n}: reduced syllables {len(r)}, independent leaf generators {2**n}, illustrative no-stem length ratio {total}')
print('BLOCKED ambient Hatcher linked Z-block realization: explicit R3 coordinates, complement avoidance, longitude/meridian map')
print('BLOCKED stem/path geometry: free-group letter length budget omits basepoint whiskers and future-stage clearance')
print('NO physical small-loop/flat-connection claim without these source geometric witnesses')
