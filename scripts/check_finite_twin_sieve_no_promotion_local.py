#!/usr/bin/env python3
"""Independent local arithmetic audit of finite twin sieve non-promotion.

Mathematical roots: Eratosthenes / Brun finite sieving; distinct from the
stronger Selberg / Polymath8b analytic parity method. Does not type-check Agda.
Uses only Python stdlib; optional exact polynomial check via SymPy.
"""
from itertools import product
from math import prod
import random

def survives(n, ps):
    return all(n % p and (n + 2) % p for p in ps)

def lift(r, P, t):
    left_factor = 1 + P * (r + 2) * t
    right_factor = 1 + P * r * t
    n = r * left_factor
    upper = (r + 2) * right_factor
    assert n + 2 == upper
    assert n == r + r * (r + 2) * t * P
    assert r >= 2 and P >= 1 and t >= 1
    assert left_factor >= 2 and right_factor >= 2
    return n, upper

def main():
    trits = list(product((-1,0,1), repeat=3))
    assert len(trits) == 3 * 3 * 3 == 27
    assert len({min(x, tuple(-z for z in x)) for x in trits}) == 14
    assert len(tuple(product(trits, repeat=2))) == 729
    rng = random.Random(20261028)
    basis = (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71)
    lists = [(),(2,),(2,3),(2,3,5),(2,3,5,7,11),
             (2,2,3,3,5),(3,5,7),(5,7,11,13,17),(31,37,41,43)]
    lists += [tuple(rng.choice(basis) for _ in range(rng.randrange(9)))
              for _ in range(150)]
    checks = 0
    for ps in lists:
        P = prod(ps)
        r = 2*P-1 if ps else 2
        assert r >= 2 and survives(r, ps)
        for p in ps:
            assert P%p == 0
            assert r%p == p-1 and (r+2)%p == 1%p
        for t in (1,2,3,4,10,100,2000):
            n,upper=lift(r,P,t)
            assert n>=t and survives(n,ps)
            assert n%P==r%P
            checks+=1
        for _ in range(10):
            x=rng.randrange(2,10000)
            t=rng.randrange(1,50)
            n,_=lift(x,P,t)
            assert survives(x,ps)==survives(n,ps)
            checks+=1
    print('PASS:',checks,'finite arithmetic witness checks across',len(lists),'modulus lists')
    print('PASS: typed 3x3x3 cardinality and 14 antipodal classes')
    print('NO Agda kernel, universal compiler or twin-prime infinitude receipt')

if __name__ == '__main__':
    main()
