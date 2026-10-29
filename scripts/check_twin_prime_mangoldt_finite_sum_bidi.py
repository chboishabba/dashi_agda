#!/usr/bin/env python3
"""Independent finite-sum BIDI oracle, not an Agda kernel receipt.

Original von Mangoldt semantics and Nat / 270 period-residue arithmetic.
No analytic positivity claim. 2026-10-29.
"""
from math import isqrt, log

def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))

def von_mangoldt(n):
    if n < 2: return 0.
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            rest = n
            while rest % p == 0:
                rest //= p
            return log(p) if rest == 1 and is_prime(p) else 0.
    return log(n)

def encode(n):
    assert n >= 0
    return divmod(n, 270)

def decode(code):
    k, r = code
    assert k >= 0 and 0 <= r < 270
    return 270 * k + r

def pair(n):
    return von_mangoldt(n) * von_mangoldt(n + 2)

def main():
    comparisons = 0
    for start in range(0, 1200, 37):
        for count in (0, 1, 2, 17, 270, 541):
            ns = range(start, start + count)
            assert sum(von_mangoldt(n) for n in ns) == sum(von_mangoldt(decode(encode(n))) for n in ns)
            assert sum(pair(n) for n in ns) == sum(pair(decode(encode(n))) for n in ns)
            comparisons += 2
    for n in range(20_000):
        assert decode(encode(n)) == n
    for k in range(80):
        for r in range(270):
            assert encode(decode((k, r))) == (k, r)
    assert encode(59)[1] == encode(329)[1]
    assert encode(59) != encode(329)
    assert pair(59) > 0 and pair(329) == 0
    print(f"PASS: {comparisons} finite sums; 20,000 Nat BIDI; 21,600 code BIDI")
    print("No assertion of positive asymptotic correlation or twin-prime infinitude.")

if __name__ == "__main__":
    main()
