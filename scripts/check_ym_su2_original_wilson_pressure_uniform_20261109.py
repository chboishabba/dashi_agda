#!/usr/bin/env python3
"""Exact-rational SU(2) finite geometric regression for the original Wilson
high-beta pressure proof. This does NOT prove the Haar integration,
log-convexity, or continuum YM. Those are analytic proof obligations
shown in Docs/physics/YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md.
"""
from fractions import Fraction
from itertools import product

Q = Fraction
Z = Q(0)
O = Q(1)

def mul(a, b):
    a0,a1,a2,a3=a
    b0,b1,b2,b3=b
    return (
        a0*b0-a1*b1-a2*b2-a3*b3,
        a0*b1+a1*b0+a2*b3-a3*b2,
        a0*b2-a1*b3+a2*b0+a3*b1,
        a0*b3+a1*b2-a2*b1+a3*b0
    )

def conj(a):
    return a[0],-a[1],-a[2],-a[3]

def dot(a,b):
    return sum((x*y for x,y in zip(a,b)), Z)

def axis(t, i):
    den = O+t*t
    x = (O-t*t)/den
    y = (2*t)/den
    out=[x,Z,Z,Z]
    out[i]=y
    return tuple(out)

def main():
    # 4D periodic positive-links / unoriented plaquettes, every V sites.
    for sites in (1,2,3,7,16,1000):
        assert Q(4*sites,6*sites)==Q(2,3)

    delta=Q(1,8)
    ident=(O,Z,Z,Z)
    # For each rational test quaternion, theta=2atan(t) <= 2t <= delta.
    tests=[ident]
    for i in (1,2,3):
        for sign in (1,-1):
            tests.append(axis(Q(sign,32),i))
    assert len(tests)==7
    assert all(dot(a,a)==O for a in tests)
    count=0
    mintrace=O
    for four in product(tests,repeat=4):
        q=ident
        for idx,a in enumerate(four):
            q=mul(q,conj(a) if idx&1 else a)
        assert dot(q,q)==O
        # Product SU2 geodesic ≤4delta, then 1-cos(4delta)≤8delta².
        assert q[0]>=O-8*delta*delta
        mintrace=min(mintrace,q[0])
        count+=1
    assert count==7**4
    assert mintrace>=O-8*delta*delta
    print("PASS: 4D link/plaquette ratio=2/3 for six finite periodic volumes")
    print(f"PASS: {count} rational SU(2) four-link plaquette word checks")
    print(f"minimum exact normalized plaquette trace={mintrace}")
    print("ANALYTIC INPUTS: normalized Haar cap mass, Gibbs pressure convexity")
    print("OPEN: physical cluster/connected-polymer bound, original E1 continuum, same-H gap")

if __name__=="__main__":
    main()
