#!/usr/bin/env python3
"""Finite pair-sieve / SSP15-vs-complete-CRT distinction.

Mathematical source roots: Eratosthenes, Brun; finite CRT local-factor
reasoning is classical. This is independently executable exact arithmetic,
not an Agda kernel proof or an analytic theorem about infinitely many primes.
"""
from math import gcd, prod

# Existing DASHI.Biology.SignedSSPFRACTRANWeaveExact.canonicalSSPPrimes.
SSP15 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71)
PREFIXES = ((2,), (2, 3), (2, 3, 5), (2, 3, 5, 7),
            (2, 3, 5, 7, 11), (2, 3, 5, 7, 11, 13))


def check():
    # In a twin-offset pair (n,n+2), 2 excludes one local residue;
    # each odd prime excludes exactly two *distinct* residues.
    for p in SSP15:
        survivors = [r for r in range(p) if r % p and (r + 2) % p]
        expected = p - (1 if p == 2 else 2)
        assert len(survivors) == expected, (p, len(survivors), expected)
        assert 0 not in survivors
        if p > 2:
            assert (p - 2) not in survivors

    for primes in PREFIXES:
        modulus = prod(primes)
        actual = sum(gcd(n * (n + 2), modulus) == 1
                     for n in range(modulus))
        expected = prod(p - (1 if p == 2 else 2) for p in primes)
        assert actual == expected, (primes, actual, expected)
        print(f"CRT pair sieve: {primes}; total={modulus}, survivors={actual}")

    assert SSP15 != tuple(p for p in range(2, 72) if
                          all(p % d for d in range(2, int(p ** 0.5) + 1)))
    # SSP15 misses primes 37, 43, 53, 61, 67 below 72.
    assert all(p not in SSP15 for p in (37, 43, 53, 61, 67))
    # 43*53 survives the entire SSP15 basis (both pair endpoints), yet
    # is composite. This is a direct witness that 15-prime screening
    # does not establish primality or twin-prime infinitude.
    n = 43 * 53
    assert n == 2279 and gcd(n * (n + 2), prod(SSP15)) == 1
    assert n % 43 == 0 and n % 53 == 0
    print("SSP15 incomplete-sieve witness: n=2279=43*53, n+2=2281")
    print("status: finite checks only; no general CRT-in-Agda or gap proof")


if __name__ == "__main__":
    check()
