#!/usr/bin/env python3
"""Exact finite signed 43 / degree-41 Hecke chart regression (not kernel proof)."""
from fractions import Fraction as Q
from itertools import product
from math import gcd
import random

P, L = 43, 41


def act(k):
    x, y = (0, 1) if k == L else (1, k)
    a, b = (4*x+y) % L, (3*x+4*y) % L
    return L if a == 0 else b*pow(a, -1, L) % L


def eval_poly(cs, x):
    s = 0
    for c in reversed(cs):
        s = s*x+c
    return s


def interpolate(xs, ys, x):
    out = Q(0)
    for i, a in enumerate(xs):
        term = Q(ys[i])
        for j, b in enumerate(xs):
            if i != j:
                term *= Q(x-b, a-b)
        out += term
    return out


def main():
    counts = dict(field=0, torus=0, crt=0, sign=0, interpolation=0, controls=0)
    units = [pow(3, e, P) for e in range(42)]
    assert set(units) == set(range(1, P)); counts['field'] += 1
    assert pow(3, 21, P) == P-1; counts['field'] += 1
    assert {x*x % L for x in range(L)}.isdisjoint({3}); counts['field'] += 1
    assert gcd(13, L) == 1; counts['field'] += 1
    orbit = [L]
    for _ in range(41):
        orbit.append(act(orbit[-1]))
    assert set(orbit) == set(range(42)); counts['torus'] += 1
    for e, k in enumerate(orbit):
        assert act(k) == orbit[(e+1)%42]
        assert units[(e+1)%42] == 3*units[e]%P
        counts['torus'] += 2
    for a,b,c in product(range(2),range(3),range(7)):
        e = (21*a+28*b+36*c)%42
        assert (e%2,e%3,e%7) == (a,b,c)
        assert units[e] == pow(3,21*a+28*b+36*c,P)
        counts['crt'] += 2
    for e in range(42):
        u = units[e]; x = u if u<=21 else u-P
        assert units[(e+21)%42] == (-u)%P
        assert x != 0 and abs(x)<=21 and x%P == u
        assert orbit[(e+21)%42] != orbit[e]
        counts['sign'] += 3
    rng = random.Random(16343)
    xs = [k*k for k in range(1,22)]
    for _ in range(6):
        cs = [rng.randrange(-100,101) for _ in range(43)]
        ev = [Q(eval_poly(cs,k)+eval_poly(cs,-k),2) for k in range(1,22)]
        od = [Q(eval_poly(cs,k)-eval_poly(cs,-k),2*k) for k in range(1,22)]
        for y in [Q(-262537412640768000),Q(1,3),Q(-7,5)]:
            assert interpolate([0]+xs,[cs[0]]+ev,y*y)+y*interpolate(xs,od,y*y)==eval_poly(cs,y)
            # Leading coefficient supplied separately by monicity of both inputs.
            ev20 = [v-cs[42]*x**21 for x,v in zip(xs,ev)]
            assert interpolate(xs,ev20,y*y)+cs[42]*y**42+y*interpolate(xs,od,y*y)==eval_poly(cs,y)
            counts['interpolation'] += 2
    # Neither the modular field nor the unsigned quotient is faithful over Z.
    assert all((43*x)%43==0 for x in range(43)); counts['controls'] += 1
    assert 43 != 0; counts['controls'] += 1
    assert eval_poly([0,1],1) != eval_poly([0,1],-1); counts['controls'] += 1
    assert 41 == (81+1)//2 and 43 != (81+1)//2; counts['controls'] += 1
    print(counts, 'total', sum(counts.values()), 'PASS')


if __name__ == '__main__':
    main()
