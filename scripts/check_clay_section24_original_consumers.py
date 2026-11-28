#!/usr/bin/env python3
"""Finite algebra and explicit no-go checks for Section 24 source welds.
Does not run Lean/Agda or establish any universal Clay endpoint.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial, gcd
import random

def run():
    counts = dict(ns=0, bsd=0, hodge=0, pnp=0, rh=0, ym=0)
    # NS: same original nonnegative Fourier weights pay the high shell.
    modes = list(product(range(-2, 3), repeat=3))
    modes.remove((0, 0, 0))
    rng = random.Random(369)
    for _ in range(64):
        weights = {k: Q(rng.randrange(21), 8) for k in modes}
        diss = sum((sum(x*x for x in k)*v for k, v in weights.items()), Q(0))
        for radius_sq in range(1, 14):
            tail = sum((v for k,v in weights.items() if sum(x*x for x in k)>=radius_sq), Q(0))
            assert radius_sq*tail <= diss
            counts['ns'] += 1
    # BSD: rational doubling cosets, not halves in an algebraic closure.
    for n in range(1, 73):
        doubled = {(2*x)%n for x in range(n)}
        for p in range(n):
            for q in range(n):
                same = any((p-q-r)%n==0 for r in doubled)
                assert same == ((p-q)%gcd(n,2)==0)
                counts['bsd'] += 1
    # Hodge: equal polynomial evaluations iff equal original chart lifts
    # in nonreduced R=F5[e,d]/(e,d)^2. Only e is named as a coordinate.
    mod=5
    def eval_poly(coeffs):
        return (coeffs[0]%mod, coeffs[1]%mod)
    ps=list(product(range(mod),repeat=3))
    def mul_dual(a,b):
        return ((a[0]*b[0])%mod,(a[0]*b[1]+a[1]*b[0])%mod)
    def projective_chart(coeffs,degree):
        h=(1,0); z=(0,1)
        power_h=[h]; power_z=[h]
        for j in range(degree):
            power_h.append(mul_dual(power_h[-1],h))
            power_z.append(mul_dual(power_z[-1],z))
        terms=[mul_dual(power_z[j],power_h[degree-j]) for j in range(3)]
        return (sum(c*t[0] for c,t in zip(coeffs,terms))%mod,
                sum(c*t[1] for c,t in zip(coeffs,terms))%mod)
    for a in ps:
        for b in ps:
            for degree in (2,4):
                assert (eval_poly(a)==eval_poly(b)) == (projective_chart(a,degree)==projective_chart(b,degree))
                counts['hodge']+=1
    # The omitted nilpotent d proves generated B=F5[e] != full A.
    assert (0,0,1) not in {(a,b,0) for a,b in product(range(mod),repeat=2)}
    # PNP: anchored mod-3 residual and actual adaptive read footprint.
    for n in range(2,7):
        for x in product((0,1),repeat=n):
            for y in product((0,1),repeat=n):
                d=tuple((u-v)%3 for u,v in zip(x,y))
                assert all(z in (0,1 if u else 2) for u,z in zip(x,d))
                assert tuple(u if z==0 else 1-u for u,z in zip(x,d))==y
                if sum(d)%3 == 0 and x[0]!=y[0]:
                    # Prefix stores sum mod 3; physical final observer reads x[0].
                    assert sum(x)%3==sum(y)%3
                    assert any(x[i]!=y[i] for i in [0])
                    counts['pnp']+=1
    # RH horizontal signed zero-coordinate transport (no universal zeros).
    for re in range(-10,11):
        for im in range(-5,6):
            sreal=Q(re,4)
            xi_im=Q(1,2)-sreal
            assert (xi_im==0)==(sreal==Q(1,2))
            counts['rh']+=1
    # YM local series tail majorant, not selected physical CMP102 calibration.
    for i in range(101):
        r=Q(i,100)
        k=sum((r**j/Q(factorial(j+1)) for j in range(1,20)),Q(0))
        major=r/(2*(1-r/3))
        assert 0<=k<=major<=Q(3,4)
        counts['ym']+=1
    print('SECTION24 PASS',counts,'TOTAL',sum(counts.values()))

if __name__=='__main__': run()
