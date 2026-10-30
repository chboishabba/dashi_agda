#!/usr/bin/env python3
"""Exact finite FRACTRAN denominator / 270-fibre / twin consumer regression.

Classical arithmetic and FRACTRAN: John H. Conway (1987). Reuses DASHI's
Typed SSP15 valuations, CertifiedPrimePairModulusExact and original
FRACDASHNumericInterpreterTargetExact first-applicable semantics.

The two-rule executable rack (1/7, 1/47) is NOT Conway PRIMEGAME and is
NOT a proof of general primality. Complete bounded trial-division racks
are separately constructed for each finite X. The rack length grows with
X; no cofinal prime-pair lower bound is obtained. Do not promote a
bounded executable test to a twin-prime infinitude theorem.
"""
from math import isqrt


def prime_denominators(bound):
    sieve = [True] * (bound + 1)
    if bound >= 0:
        sieve[0] = False
    if bound >= 1:
        sieve[1] = False
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            sieve[p*p:bound+1:p] = [False] * len(sieve[p*p:bound+1:p])
    return [p for p in range(2, bound + 1) if sieve[p]]


def first_applicable_denominator(n, denominators):
    return next((p for p in denominators if n % p == 0), None)


def is_prime_arithmetic(n):
    return n >= 2 and first_applicable_denominator(
        n, prime_denominators(isqrt(n))) is None


def two_rule_step(n):
    p = first_applicable_denominator(n, (7, 47))
    return None if p is None else (p, n // p)


def wheel_survives(n):
    return all(n % p and (n + 2) % p for p in (2, 3, 5))


def audit():
    assert 59 % 270 == 329 % 270 == 59
    assert divmod(59, 270) == (0, 59)
    assert divmod(329, 270) == (1, 59)
    assert two_rule_step(329) == (7, 47)
    assert two_rule_step(59) is None
    assert is_prime_arithmetic(59) and is_prime_arithmetic(61)
    assert not is_prime_arithmetic(329)
    assert 7 * 47 == 329

    for x in (100, 1000, 10000):
        gate = prime_denominators(isqrt(2*x+2))
        assert all(p < x for p in gate)
        wheel_count = twin_count = 0
        for n in range(x, 2*x):
            start_pass = first_applicable_denominator(n, gate) is None
            end_pass = first_applicable_denominator(n+2, gate) is None
            actual_twin = is_prime_arithmetic(n) and is_prime_arithmetic(n+2)
            assert (start_pass and end_pass) == actual_twin
            wheel_count += bool(wheel_survives(n))
            twin_count += bool(actual_twin)
        assert twin_count <= wheel_count
        print(dict(window_start=x, denominator_gates=len(gate),
                   wheel_survivors=wheel_count, actual_twin_starts=twin_count,
                   surviving_composites=wheel_count-twin_count))

    print("PASS: finite FRACTRAN/radix residual and true twin readout;"
          " no analytic cofinal-separation or infinitude theorem")


if __name__ == "__main__":
    audit()
