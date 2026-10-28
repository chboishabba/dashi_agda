#!/usr/bin/env python3
"""Independent exact-number execution audit for signed SSP ±2 exponent macros.

Attribution:
- Conway's PRIMEGAME produces 2^p at intermittent steps (1987 FRACTRAN).
- chboishabba/FRACDASH BRIDGE_CORRECTNESS.md owns signed register/paired-prime semantics.
- chboishabba/dashi_agda SignedSSPFRACTRANWeaveExact owns signed orientation vocabulary.
- This script independently tests arithmetic FRACTRAN fragments and their
  boundary. It DOES NOT certify Agda declarations or prove prime infinitude.
"""
from math import isqrt

CONWAY_GUY_VARIANT = (
    (17,91),(78,85),(19,51),(23,38),(29,33),(77,29),(95,23),
    (77,19),(1,17),(11,13),(13,11),(15,14),(15,2),(55,1)
)

def enabled(x, rule):
    a,b=rule
    return x % b == 0

def step(x, rules):
    for i, (a,b) in enumerate(rules):
        if x % b == 0:
            return (x//b*a, i)
    return None

def execute(x, rules, limit=100000):
    trace=[x]
    for i in range(limit):
        move=step(x,rules)
        if move is None:
            return trace
        x,index=move
        trace.append(x)
    raise AssertionError("unexpected nonhalting macro")

def is_prime(x):
    return x>=2 and all(x%d for d in range(2,isqrt(x)+1))

def primegame(steps=20000):
    x=2
    result=[]
    for i in range(steps+1):
        if x>2 and x&(x-1)==0:
            result.append((i,x.bit_length()-1,x))
        next_step=step(x,CONWAY_GUY_VARIANT)
        if next_step is None: break
        x,_=next_step
    return result

def verify():
    emit=primegame()
    assert [p for _,p,_ in emit] == [2,3,5,7,11,13,17,19,23]
    assert [tick for tick,_,_ in emit] == [
        19,69,280,707,2363,3876,8068,11319,19201
    ]
    for p in range(2,256):
        x=2**p*9
        t_plus=execute(x, ((2,3),))
        t_minus=execute(x, ((1,6),))
        assert t_plus == [9*2**p,6*2**p,4*2**p], (p,t_plus)
        assert t_minus == [9*2**p,3*2**(p-1),2**(p-2)], (p,t_minus)
        assert t_plus[-1] == 2**(p+2)
        assert t_minus[-1] == 2**(p-2)
        assert not enabled(t_plus[-1],(2,3))
        assert not enabled(t_minus[-1],(1,6))
        for tr, frac in ((t_plus,(2,3)), (t_minus,(1,6))):
            a,b=frac
            for prior,next in zip(tr,tr[1:]):
                assert prior*a == next*b and prior%b==0
    # Subtraction is not a 2-step Nat programme for p=0 or 1.
    assert execute(9,((1,6),)) == [9]
    assert execute(18,((1,6),)) == [18,3]
    # Signed FRACDASH R3 state-tag program is a distinct readout.
    assert execute(23,((17,23),(19,17))) == [23,17,19]
    assert all(is_prime(p) for _,p,_ in emit)
    # A generated prime can have a composite shifted neighbour.
    assert is_prime(13) and not is_prime(13+2)
    assert is_prime(3) and is_prime(3+2)
    assert is_prime(5) and is_prime(5+2)
    print('Conway/Guy ordered PRIMEGAME: 9 emitted prime exponents through tick 19201: PASS')
    print('Signed SSP ±2 exact integer macro: 254 input exponents 2..255: PASS')
    print('All 508 two-step traces: guards, products, final outputs, halting: PASS')
    print('Nat subtraction p=0,1 stops early; p>=2 works: PASS')
    print('FRACDASH signed R3 tag transition 23 -> 17 -> 19: PASS')
    print('No analytic prime-pair claim; no Agda kernel receipt')

if __name__=='__main__':
    verify()
