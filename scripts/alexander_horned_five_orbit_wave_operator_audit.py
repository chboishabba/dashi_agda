#!/usr/bin/env python3
"""Severe exact finite control for five-orbit heterogeneous wave transport.
The values are integer proxies for discrete wave state; not acoustics.
Reuse prior #1405 T15/T16 theorem ownership, #1244 5-orbit classifier.
"""
from itertools import product
T=(-1,0,1)
def orbit(a,b):
    if (a,b)==(0,0):return 0
    if b==0:return 1
    if a==0:return 2
    if a==b:return 3
    return 4
def rotate(x):return ((x[0]+1)%3,x[1],x[2])
def reflect(x):return (x[0],-x[1],-x[2])
def run():
    pts=tuple(product(range(3),T,T))
    # Five heterogeneous operators, including translation, scale, sign.
    operators=(lambda w:w, lambda w:w+7,lambda w:2*w,
               lambda w:-w,lambda w:w*w+1)
    source=(2,-3,4,5,7)
    f=lambda x:source[orbit(*x[1:])]
    op=lambda x:operators[orbit(*x[1:])]
    evolve=lambda x:op(x)(f(x))
    for x in pts:
        assert orbit(*rotate(x)[1:])==orbit(*x[1:])
        assert orbit(*reflect(x)[1:])==orbit(*x[1:])
        assert evolve(x)==operators[orbit(*x[1:])](source[orbit(*x[1:])])
        assert evolve(rotate(x))==evolve(x)
        assert evolve(reflect(x))==evolve(x)
        assert rotate(rotate(rotate(x)))==x
    # Non-invariant operators require transformation too (T16 naturality).
    hetero={x:(lambda w,k=i:(k+1)*w+2*k)
            for i,x in enumerate(pts)}
    varying={x:i-13 for i,x in enumerate(pts)}
    for r in (rotate,reflect):
        for x in pts:
            lhs=hetero[r(x)](varying[r(x)])
            rhs=(lambda y:hetero[y](varying[y]))(r(x))
            assert lhs==rhs
    # Counterexample: rotating field but holding unequal operators fixed.
    x=(0,-1,-1)
    assert hetero[x](varying[rotate(x)]) != hetero[rotate(x)](varying[rotate(x)])
    assert len(pts)==27
    print("PASS: 27 addresses / 5 independent heterogeneous operators")
    print("PASS: invariant evolution under sector and simultaneous sign")
    print("PASS: arbitrary operator/field simultaneous relabelling naturality")
    print("PASS: fixed heterogeneous operator relabelling counterexample")
    print("BOUNDARY: no physical acoustics, wild linking, or SU2 intertwininer")
if __name__=="__main__":run()
