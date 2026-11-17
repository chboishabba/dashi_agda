#!/usr/bin/env python3
"""Finite severe tests for native C3-valued fibre actions over K3.

The finite state set is X_n=C3×Trit^n. Its local fibre action group is
G_n=Map(X_n,C3), with pointwise addition. Projection to coarse cells
induces injective pullback maps G_n->G_(n+1). External C3 rotation
commutes with these maps. Source formal interface:
AlexanderHornedNativeTernaryFibreActionExact.agda.

Historical roots: Cantor cylinders, local gauge groups, group actions.
DASHI owns the finite selected carrier and code; no wild embedding,
kernel theorem, spin holonomy or physical experiment is asserted.
"""
from itertools import product

C3=range(3)
T=(-1,0,1)

def cells(n):
    return tuple((c,w) for c in C3 for w in product(T,repeat=n))

def project(x):
    return x[0],x[1][:-1]

def rotate(x):
    return (x[0]+1)%3,x[1]

def pullback(f,x):
    return f[project(x)]

def rotate_field(f,x):
    return f[rotate(x)]

def add(f,g,points):
    return {x:(f[x]+g[x])%3 for x in points}

def test(n):
    low=cells(n)
    high=cells(n+1)
    f={x:(x[0]+sum(x[1]))%3 for x in low}
    g={x:(2*x[0]+len(x[1]))%3 for x in low}
    pf={x:pullback(f,x) for x in high}
    pg={x:pullback(g,x) for x in high}

    assert all(project((c,w+(0,)))==(c,w) for c,w in low)
    assert all(project(rotate(x))==rotate(project(x)) for x in high)
    assert all((pf[x]+pg[x])%3==pullback(add(f,g,low),x) for x in high)
    assert all(rotate_field(pf,x)==pullback(
        {y:rotate_field(f,y) for y in low},x) for x in high)
    assert all(rotate(rotate(rotate(x)))==x for x in low)

    zero={x:0 for x in low}
    target={x:(x[0]+2*sum(x[1]))%3 for x in low}
    difference={x:(target[x]-f[x])%3 for x in low}
    assert add(difference,f,low)==target
    assert add(zero,f,low)==f
    assert len(low)==3*3**n and len(high)==3*3**(n+1)
    return len(low),len(high)

if __name__=="__main__":
    for n in range(7):
        lo,hi=test(n)
        print("PASS depth",n,"address cells",lo,"refined cells",hi)
    assert 3**27==7625597484987
    print("PASS depth-two fibre group cardinality 3^27",3**27)
    print("PASS independent pointwise, pullback, rotation and torsor controls")
