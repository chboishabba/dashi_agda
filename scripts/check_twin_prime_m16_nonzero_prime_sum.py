#!/usr/bin/env python3
"""Independent finite M16 oracle: nonzero prime-only sum iff twin in window.
No statement about arbitrarily late future windows is proved by finite tests.
"""
from math import isqrt
from random import Random
from collections import Counter

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def main():
    rng = Random(27016)
    cases = [(0, 0), (59, 1), (25, 1), (269, 0), (269, 2), (7000, 300)]
    cases += [(rng.randrange(0, 14000), rng.randrange(0, 200))
              for _ in range(2200)]
    counts = Counter()
    for start, length in cases:
        prime_only_terms = [
            (n, n + 2) for n in range(start, start + length)
            if prime(n) and prime(n + 2)]
        witness = next((
            (n, n + 2) for n in range(start, start + length)
            if prime(n) and prime(n + 2)), None)
        assert (witness is None) == (len(prime_only_terms) == 0)
        if witness is None:
            counts["zero"] += 1
        else:
            assert start <= witness[0] < start + length
            assert prime(witness[0]) and prime(witness[0] + 2)
            counts["nonzero"] += 1
    print({"status": "PASS", "finite_windows": len(cases),
           "counts": dict(counts),
           "unbounded_nonzero_sums_proved": False,
           "agda_kernel_verified": False})

if __name__ == "__main__":
    main()
