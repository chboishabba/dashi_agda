#!/usr/bin/env python3
"""Exact-fraction finite spin-turn audit.

The Q8->V4 finite cover encodes the central sign of the lift of the
continuous 360-degree rotation; it does not construct the continuous
SU2->SO3 universal cover or classify SO3 paths.

Classical sources: Hamilton quaternions, SU2/Spin3 double cover.
Repo owners: FiniteQuaternionDoubleCover; SU2SO3IrrepDimensionExact;
AlexanderHornedQuaternionC3SpinExact.
"""
from fractions import Fraction

ZERO = Fraction(0)
ONE = Fraction(1)
HALF = Fraction(1, 2)
IDENTITY = (ONE,ZERO,ZERO,ZERO)
NEGATIVE_IDENTITY = (-ONE,ZERO,ZERO,ZERO)
I=(ZERO,ONE,ZERO,ZERO)
J=(ZERO,ZERO,ONE,ZERO)
K=(ZERO,ZERO,ZERO,ONE)

def multiply(a,b):
    a0,a1,a2,a3=a
    b0,b1,b2,b3=b
    return (
        a0*b0-a1*b1-a2*b2-a3*b3,
        a0*b1+a1*b0+a2*b3-a3*b2,
        a0*b2-a1*b3+a2*b0+a3*b1,
        a0*b3+a1*b2-a2*b1+a3*b0
    )
def power(q,n):
    z=IDENTITY
    for _ in range(n):z=multiply(z,q)
    return z

def audit():
    assert multiply(NEGATIVE_IDENTITY,NEGATIVE_IDENTITY)==IDENTITY
    assert multiply(I,I)==NEGATIVE_IDENTITY

    Q8={
        IDENTITY,NEGATIVE_IDENTITY,
        I,tuple(-x for x in I),
        J,tuple(-x for x in J),
        K,tuple(-x for x in K)
    }
    assert len(Q8)==8
    assert {multiply(x,y) for x in Q8 for y in Q8}==Q8
    def spatial_fibre(q):
        if q in (IDENTITY,NEGATIVE_IDENTITY):return 0
        if q in (I,tuple(-x for x in I)):return 1
        if q in (J,tuple(-x for x in J)):return 2
        if q in (K,tuple(-x for x in K)):return 3
        raise AssertionError("not in Q8")
    fibres={i:[q for q in Q8 if spatial_fibre(q)==i] for i in range(4)}
    assert sorted(map(len,fibres.values()))==[2,2,2,2]
    assert spatial_fibre(IDENTITY)==spatial_fibre(NEGATIVE_IDENTITY)==0
    assert IDENTITY!=NEGATIVE_IDENTITY

    q=(HALF,HALF,HALF,HALF)
    qinverse=(HALF,-HALF,-HALF,-HALF)
    negative_q=tuple(-v for v in q)
    assert multiply(q,qinverse)==IDENTITY
    assert power(q,3)==NEGATIVE_IDENTITY
    assert power(q,6)==IDENTITY
    assert power(negative_q,3)==IDENTITY
    assert all(multiply(multiply(q,x),qinverse)==y
               for x,y in ((I,J),(J,K),(K,I)))
    print("PASS Q8->V4: four fibres each size 2; +/-1 project to same identity")
    print("PASS spin 360: central -1 != +1; spin 720: (-1)^2 = +1")
    print("PASS 120deg horn rotor: 3 turns -> -1; 6 turns -> +1")
    print("PASS negative signed 120deg lift: cube +1, same spatial rotation")
    print("NOT tested: continuous SU2/SO3 covering paths, geometric wild pi1, Agda kernel")

if __name__=="__main__":audit()
