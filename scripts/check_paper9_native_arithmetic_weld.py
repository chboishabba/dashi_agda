#!/usr/bin/env python3
"""Exact reference regression for native Paper 9 source welds; not a kernel proof."""
from fractions import Fraction as F
from math import factorial, isqrt
from random import Random
import sympy as s

A, B, C = 13591409, 545140134, 640320**3


def bit(t, r):
    return 2*r + int((2*r+1)**2 <= 4*t)


def main():
    x = s.symbols('x')
    mag = 24*(2*x+1)*(6*x+1)*(6*x+5)
    block3 = s.prod(3*x+i for i in range(1,4))
    block6 = s.prod(6*x+i for i in range(1,7))
    assert s.expand(mag*block3-block6) == 0
    t, q, r, d, w, g = s.symbols('t q r d w g')
    assert s.expand(((t*q*r+w*g)*d)-(t*d*q*r+w*g*d)) == 0
    rng = Random(163)
    targets = list(range(2048))+[rng.getrandbits(k) for k in range(1,1025)]
    for t in targets:
        r = isqrt(t); R = bit(t,r)
        assert R*R <= 4*t < (R+1)**2
        assert 2*r <= R and R+1 <= 2*(r+1)
        assert R == isqrt(4*t)
    t, r = 160080, 400
    roots = []
    for k in range(4097):
        assert t == 10005*2**(2*(k+2))
        assert r == isqrt(t)
        assert r*r <= t < (r+1)**2
        roots.append(r)
        t, r = 4*t, bit(t,r)
    P, Q, T = 1, 1, 0
    fact_sum = F(0)
    raw = [(P,Q,T)]
    for n in range(513):
        p, q = (1,1) if n == 0 else (-24*(2*n-1)*(6*n-5)*(6*n-1), C*n**3)
        P *= p; Q *= q; T = T*q+P*(A+B*n)
        raw.append((P,Q,T))
        assert P*factorial(3*n) == (-1)**n*factorial(6*n)
        assert Q == C**n*factorial(n)**3
        term = F((-1)**n*factorial(6*n), C**n*factorial(3*n)*factorial(n)**3)
        assert F(P,Q) == term
        fact_sum += term*(A+B*n)
        assert F(T,Q) == fact_sum
    for n in range(512):
        p,q,t = raw[n]; p1,q1,t1 = raw[n+1]; p2,q2,t2 = raw[n+2]
        w = p1
        gap = (A+B*n)*(C*(n+1)**3)-24*(2*n+1)*(6*n+1)*(6*n+5)*(A+B*(n+1))
        assert gap > 0
        assert t1*q-t*q1 == w*(A+B*n)*q
        assert t2*q-t*q2 == w*gap*q
        lo,hi = sorted((F(t,q),F(t1,q1)))
        l2,u2 = sorted((F(t1,q1),F(t2,q2)))
        assert lo <= l2 <= u2 <= hi
    previous = None
    for k,r in enumerate(roots):
        scale=2**(k+2); n=1+(k+4)//41
        _,q,t=raw[n]; _,q1,t1=raw[n+1]
        lo,hi=sorted((F(t,q),F(t1,q1)))
        W=(F(426880*r,scale)/hi,F(426880*(r+1),scale)/lo)
        assert W[0]<=W[1]
        if previous is not None:
            assert previous[0]<=W[0]<=W[1]<=previous[1]
        previous=W
    print('2 universal polynomial normal forms PASS')
    print('3072 arbitrary double-floor cases; 4097 literal dyadic root stages PASS')
    print('513 signed factorial P/Q/product/sum identities; 512 signed adjacent/two-step crosses and nesting PASS')
    print('4097 literal reciprocal windows, 4096 inclusions PASS')


if __name__ == '__main__':
    main()
