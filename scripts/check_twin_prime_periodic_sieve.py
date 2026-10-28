#!/usr/bin/env python3
"""Exact finite regression for a coprimality-free pair sieve period.

The Agda proof owner uses the standard modular theorem
[m+kn]%n≡m%n. A finite regression cannot replace its kernel check.
Distinct source authority: Eratosthenes/Brun and Agda's modular arithmetic.
"""
from math import lcm, prod
from itertools import product

SSP15 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71)

def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))

def survive(n, axes):
    return all(n % p and (n+2) % p for p in axes)

def check():
    sets = ((2, 3), (2, 3, 5), (2, 3, 37), (2, 3, 43),
            (2, 3, 37, 43), (5, 7, 11), (2, 2, 3, 3),
            (3, 3, 5, 7), (2, 3, 5, 7, 11, 13))
    for axes in sets:
        assert all(is_prime(p) for p in axes)
        period = prod(axes)
        minimal_common = lcm(*axes)
        assert period % minimal_common == 0
        # Repeat from many phases and multipliers, not just the base block.
        for n in range(0, 150):
            b = survive(n, axes)
            for k in (0, 1, 2, 7, 19):
                assert survive(n + k*period, axes) == b, (axes, n, k)
                assert survive(n + k*minimal_common, axes) == b, (axes, n, k)
        if period <= 30030:
            count = sum(survive(n, axes) for n in range(period))
            if len(set(axes)) == len(axes):
                expected = prod(p-(1 if p == 2 else 2) for p in axes)
                assert count == expected, (axes,count,expected)
            else:
                count_lcm = sum(survive(n, axes) for n in range(minimal_common))
                assert count == count_lcm*(period//minimal_common)
    # Commuting two local residue filters is symmetry, not prime generation.
    for a,b in product((2,3,5,37,43), repeat=2):
        for n in range(0,120):
            assert survive(n,(a,b)) == survive(n,(b,a))
    # Finite survival never guarantees primality.
    n=43*53
    assert not is_prime(n) and survive(n,SSP15)
    print('arbitrary-period exact regression: 9 prime lists, 2,3,37,43 and repeated axes')
    print('period product and lcm; local-filter commutation; composite counterexample: PASS')
    print('claim boundary: finite checks, no kernel typecheck or twin infinitude')

if __name__ == '__main__':
    check()
