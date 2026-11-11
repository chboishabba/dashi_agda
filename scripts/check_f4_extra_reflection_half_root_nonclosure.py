#!/usr/bin/env python3
"""Selected extra W(F4) short-root reflection cannot preserve F4 half16.

All F4 doubled-coordinate roots: 8 axis short (norm4), 16 half
short (norm4), 24 long (norm8). Reflection in alpha=(1,1,1,1)
has formula r_alpha(v) = v - ((v.alpha)/2)alpha on doubled vectors.
It permutes the full 48 F4 root set, but not the 16 half-root subset.
Therefore the full 240=nonemptySupport15 x Half16 standard B4
bijection is NOT automatically a full W(F4) equivariant bijection.
"""
from itertools import combinations,product

def roots():
    axis=set()
    for i in range(4):
        for a in (-2,2):
            r=[0]*4;r[i]=a;axis.add(tuple(r))
    half=set(product((-1,1),repeat=4))
    long=set()
    for i,j in combinations(range(4),2):
        for a,b in product((-2,2),repeat=2):
            r=[0]*4;r[i],r[j]=a,b;long.add(tuple(r))
    assert (len(axis),len(half),len(long))==(8,16,24)
    allroots=axis|half|long
    assert len(allroots)==48
    return axis,half,long,allroots

def reflect(v,alpha=(1,1,1,1)):
    d=sum(x*y for x,y in zip(v,alpha))
    assert d%2==0
    return tuple(x-(d//2)*y for x,y in zip(v,alpha))

def test():
    axis,half,long,allroots=roots()
    assert {reflect(v) for v in allroots}==allroots
    assert {reflect(v) for v in long}==long
    images={reflect(v) for v in half}
    assert len(images&half)==8
    assert len(images&axis)==8
    assert reflect((1,1,1,-1))==(0,0,0,-2)
    assert reflect(reflect((1,1,1,-1)))==(1,1,1,-1)
    print("PASS: reflection permutes all 48 F4 roots and all 24 long roots")
    print("PASS: half16 maps to 8 half roots plus 8 axis short roots")
    print("CONCLUSION: B4 half16 action does not extend by this standard F4 generator")
    print("OPEN: actual #1106 E6-folded producer same-group action and 240 target")

if __name__=="__main__":test()
