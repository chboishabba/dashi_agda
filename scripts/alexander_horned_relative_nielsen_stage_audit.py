#!/usr/bin/env python3
"""Exact elementary Nielsen sequence for ternary parent-meridian word.

Finite free-group certificate, NOT a PL homeomorphism or a three-dimensional
embedded wild satellite. Historical owners: classical Nielsen transformations,
Hensel's handlebody primer; Hatcher's separate BINARY horn construction.
"""
from itertools import product
def red(w):
    out=[]
    for x in w:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return tuple(out)
def inv(w): return tuple(-x for x in reversed(w))
def mul(*ws): return red(tuple(x for w in ws for x in w))
def comm(a,b): return mul(a,b,inv(a),inv(b))
def image(w,m): return mul(*(m[abs(i)] if i>0 else inv(m[-i]) for i in w))
A=(1,); B=(2,); C=(3,)
w=mul(comm(A,B),comm(B,C))
p=mul(A,B,inv(A),C)
u=inv(B); v=mul(inv(C),A); z=C
assert w==(1,2,-1,3,-2,-3)
assert mul(inv(p),w,p)==comm(u,v)
states=[(A,B,C)]
states.append((A,inv(B),C))                 # flip b orientation
states.append((mul(inv(C),A),inv(B),C))    # slide a over c
states.append((states[-1][1],states[-1][0],C)) # interchange handles
assert states[-1]==(u,v,z)
old_in_new={1:(3,2),2:(-1,),3:(3,)}
new_in_old={1:u,2:v,3:z}
count=0
for n in range(6):
    for word in product((-3,-2,-1,1,2,3),repeat=n):
        wr=red(word)
        assert image(image(wr,old_in_new),new_in_old)==wr
        assert image(image(wr,new_in_old),old_in_new)==wr
        count+=1
assert count==9331
assert inv(B)!=B
print("PASS: 3 elementary Nielsen moves, inverse map, conjugator")
print("PASS: exhaustive",count,"words lengths 0..5")
print("BOUNDARY: no ambient PL map, cap-fixed support, 3-child linked satellite or wild limit")
