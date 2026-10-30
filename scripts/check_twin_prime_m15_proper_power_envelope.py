#!/usr/bin/env python3
"""CT10/CT11/CT13 finite arithmetic oracle for proper-power residual bounds.

All integer support inequalities are checked exactly. Weighted logs are
only a *numerical* sanity check, NOT a proof of an ordered-real estimate.
Reuses formal proof owners:
  RiemannPrimePowerArithmetic, FiniteNatFloorSquareRootExact,
  TwinPrimeProperPowerFloorRootBoundExact,
  TwinPrimeProperPowerBinaryExponentLowerExact.
No sieve periodicity -> twin-prime positivity promotion.
"""
from math import isqrt, log

def primes_upto(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[0] = flags[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p:limit+1:p] = b"\x00" * (1 + (limit - p*p)//p)
    return [p for p in range(2, limit + 1) if flags[p]]

def prime_powers_upto(limit):
    base, exponent = [0] * (limit + 1), [0] * (limit + 1)
    for p in primes_upto(limit):
        power, k = p, 1
        while power <= limit:
            assert base[power] in (0, p), ("nonunique prime base", power)
            base[power], exponent[power] = p, k
            power *= p
            k += 1
    return base, exponent

def audit(max_x=40000):
    limit = 2 * max_x + 2
    base, exponent = prime_powers_upto(limit)
    xs = [2,3,5,10,25,59,100,270,500,1000,2700,5000,10000,20000,40000]
    xs += list(range(19, max_x, 173))
    windows, error_terms, weighted_terms = 0, 0, 0
    for x in sorted(set(xs)):
        u = 2*x + 2
        root, binary_log_floor = isqrt(u), u.bit_length() - 1
        proper_values = [n for n in range(2,u+1) if exponent[n] >= 2]
        for n in proper_values:
            p, k = base[n], exponent[n]
            assert p <= root and 2**k <= u
        assert len(proper_values) <= root * binary_log_floor
        count, weighted_error = 0, 0.0
        for n in range(x,2*x):
            p,q = base[n], base[n+2]
            if not p or not q:
                continue
            weighted_terms += 1
            if exponent[n] >= 2 or exponent[n+2] >= 2:
                count += 1
                weighted_error += log(p) * log(q)
        # Exact integer support count: a shifted union of two proper-power sets.
        assert count <= 2 * len(proper_values)
        assert count <= 2 * root * binary_log_floor
        # Floating-point diagnostic ONLY. Algebraic CT12/CT13 still owed.
        assert 0 <= weighted_error <= 2 * root * binary_log_floor * log(u)**2 + 1e-9
        windows += 1
        error_terms += count
    return {"status":"PASS", "checked_dyadic_windows": windows,
            "actual_proper_power_error_terms": error_terms,
            "actual_nonzero_lambda_pair_terms": weighted_terms,
            "ct10_integer_envelope_tested": True,
            "ct11_integer_count_tested": True,
            "agda_kernel_verified": False,
            "ct13_uniform_weighted_theorem_proved": False,
            "ct15_gap_two_correlation_proved": False}

if __name__ == "__main__":
    print(audit())
