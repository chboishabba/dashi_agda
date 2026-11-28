#!/usr/bin/env python3
"""Finite exact checks of the second-jet and degree-42 specialization welds.

This is not an analytic identity, native kernel proof, or full CM packet replay.
"""
from fractions import Fraction as F
from math import comb
import random
import sympy as s


def eval_poly(cs, x):
    a = 0
    for c in reversed(cs):
        a = a*x+c
    return a


def wing(cs, u, v):
    return sum(c*sum(u**k*v**(n-1-k) for k in range(n))
               for n,c in enumerate(cs))


def second(cs, u, v):
    return sum(c*sum(u**(i+j)*v**(n-2-i-j)
                     for i in range(n-1) for j in range(n-1-i))
               for n,c in enumerate(cs))


def interpolate(values, x):
    row = list(values)
    out, basis = F(0), F(1)
    for k in range(len(values)):
        out += row[0]*basis
        row = [b-a for a,b in zip(row,row[1:])]
        basis *= (x-k)/F(k+1)
    return out


def main():
    rng = random.Random(16341)
    counts = dict(diagonal=0, affine=0, euler=0, hecke_parameter=0, negative=0)
    tri = 1
    for n in range(120):
        assert tri == comb(n+2,2)
        assert 2*tri == (n+2)*(n+1)
        tri += n+2
        counts['diagonal'] += 2
    for _ in range(120):
        cs = [F(rng.randrange(-15,16)) for _ in range(rng.randrange(2,12))]
        u = F(rng.choice([-5,-3,-2,1,2,4]),7)
        v = F(rng.choice([-6,-4,-1,1,3,5]),11)
        J0 = eval_poly(cs,u)
        j0 = J0/u
        J1 = wing(cs,u,u)
        J2 = second(cs,u,u)
        j1 = (J1-j0)/u
        j2 = (J2-j1)/u
        Q = wing(cs,u,v)
        T = second(cs,u,v)
        r = (Q-j0)/v
        h = (T-j1)/v
        assert eval_poly(cs,v)/v-j0 == (v-u)*r
        assert r-j1 == (v-u)*h
        assert u*j1+j0 == J1
        assert u*j2+j1 == J2
        counts['affine'] += 4
        # Laurent polynomial j=J/q, including exponent -1.
        assert u*j1 == sum((n-1)*c*u**(n-1) for n,c in enumerate(cs))
        assert u*j1+2*u*u*j2 == sum((n-1)**2*c*u**(n-1) for n,c in enumerate(cs))
        counts['euler'] += 2
    # Exact parameter reconstruction on 43 integer nodes, with rational
    # target probes including the original signed CM center. This tests
    # interpolation, not reflection of the actual 43x43 Hecke matrix.
    K = -262537412640768000
    for _ in range(12):
        cs = [rng.randrange(-10**5,10**5) for _ in range(43)]
        values = [eval_poly(cs,k) for k in range(43)]
        for x in [F(K), F(K)+F(1,3), F(-1,7), F(7,3), F(43), F(100)]:
            assert interpolate(values,x) == eval_poly(cs,x)
            counts['hecke_parameter'] += 1
    x = s.symbols('x')
    bad = s.prod(x-k for k in range(43))
    assert all(bad.subs(x,k)==0 for k in range(43))
    assert bad.subs(x,43)!=0
    counts['negative'] += 44
    print(counts, 'total', sum(counts.values()), 'PASS')


if __name__ == '__main__':
    main()
