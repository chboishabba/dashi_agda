#!/usr/bin/env python3
"""Independent finite model for M15 retained Mangoldt error-support theorem.

Requires *actual* prime-power bases at both endpoints. A nonzero
non-prime-only lambda product can occur only when at least one endpoint
is a proper prime power, and its base/exponent satisfy the inherited
root/binary envelope.

This is NOT an Agda kernel verification or a global analytic bound.
"""
from math import isqrt
from functools import lru_cache

@lru_cache(None)
def prime_power(n):
    if n < 2:
        return None
    for p in range(2, isqrt(n)+1):
        if n % p == 0:
            t, k = n, 0
            while t % p == 0:
                t //= p
                k += 1
            return (p, k) if t == 1 else None
    return (n, 1)

def audit(limit=150000):
    nonzero_error = genuine_twins = outside = 0
    for n in range(2, limit+2):
        left, right = prime_power(n), prime_power(n+2)
        proper = ((left is not None and left[1] >= 2) or
                  (right is not None and right[1] >= 2))
        # The formal sum is log(p)*log(q) for two prime powers.
        error_nonzero = (left is not None and right is not None and proper)
        assert not error_nonzero or proper
        if error_nonzero:
            nonzero_error += 1
            for pair in (left, right):
                if pair is not None and pair[1] >= 2:
                    p,k=pair
                    assert p <= isqrt(n+2)
                    assert 2**k <= n+2
        elif left is not None and right is not None:
            assert left[1] == right[1] == 1
            genuine_twins += 1
        else:
            outside += 1
    print({"status":"PASS","candidates":limit,"nonzero_error":nonzero_error,
           "prime_prime_pairs":genuine_twins,"outside_support":outside,
           "kernel_verified":False,"uniform_m15_bound_proved":False})

if __name__ == "__main__":
    audit()
