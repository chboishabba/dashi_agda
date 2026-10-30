#!/usr/bin/env python3
"""CT15 parity-frontier exact integer oracle; NOT a twin-prime theorem.

For actual prime p, mu(p+2)=-1 iff p+2 is prime OR squarefree with
an odd number >=3 of distinct prime factors. For those composites,
the least prime factor cubed is <= p+2. This shows precisely which
arithmetic information the 2026 shifted-Mobius cancellation does not
supply.

Source: G. Lu, Z. Wang, J. Wu (14 Oct 2026), arXiv:2610.20242:
their shifted Lambda*mu cancellation is NOT shifted Lambda*Lambda
positivity. Historical Mobius/von Mangoldt priority is independent of
this DASHI source implementation. No QID/SSP/Monster identification.
"""
from math import isqrt


def least_prime_factors(limit):
    spf = list(range(limit + 1))
    for prime in range(2, isqrt(limit) + 1):
        if spf[prime] == prime:
            for n in range(prime * prime, limit + 1, prime):
                if spf[n] == n:
                    spf[n] = prime
    return spf


def factor_shape(n, spf):
    omega, Omega, squarefree = 0, 0, True
    least = spf[n]
    while n > 1:
        prime = spf[n]
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        omega += 1
        Omega += exponent
        squarefree &= exponent == 1
    return Omega, omega, squarefree, least


def run(windows=(10000, 30000, 100000, 300000, 1000000)):
    spf = least_prime_factors(2 * max(windows) + 3)
    assert factor_shape(5, spf) == (1, 1, True, 5)
    assert factor_shape(105, spf) == (3, 3, True, 3)
    assert spf[103] == 103 and spf[105] == 3

    for X in windows:
        prime_starts = negative = positive = sqfree = 0
        twins = odd_composite = rough_negative = 0
        for p in range(X, 2 * X):
            if spf[p] != p:
                continue
            prime_starts += 1
            m = p + 2
            Omega, omega, is_squarefree, least = factor_shape(m, spf)
            assert Omega >= omega >= 1
            is_twin = spf[m] == m
            mu = 0 if not is_squarefree else (-1)**omega
            prime_part = is_squarefree and omega == 1
            composite_part = is_squarefree and omega >= 3 and omega % 2 == 1
            assert (mu == -1) == (prime_part or composite_part)
            assert not (prime_part and composite_part)
            twins += is_twin
            negative += mu == -1
            positive += mu == 1
            sqfree += is_squarefree
            odd_composite += composite_part
            if composite_part:
                assert least ** 3 <= m
            rough = least ** 3 > m
            if rough and mu == -1:
                rough_negative += 1
                assert is_twin
            if is_twin:
                assert rough and mu == -1
        assert negative == twins + odd_composite
        assert rough_negative == twins
        assert negative + positive == sqfree
        print(
            dict(X=X, prime_starts=prime_starts,
                 negative_mobius=negative,
                 odd_squarefree_composite=odd_composite,
                 twin_pairs=twins,
                 rough_negative=rough_negative,
                 twin_fraction_of_negative=round(twins / negative, 6))
        )
    print("PASS: exact finite Mobius-parity and cube-roughness cuts; no analytic bound claimed")


if __name__ == "__main__":
    run()
