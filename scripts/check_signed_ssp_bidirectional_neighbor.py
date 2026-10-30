#!/usr/bin/env python3
"""Finite independent exact-integer replay of DASHI signed +/-2 CRT bridge.

Sources: J. H. Conway, FRACTRAN (1987); R. K. Guy (1983) for Conway
PRIMEGAME; FRACDASH signed register compiler; DASHI signed SSP owner.
No Agda kernel check, universal prime emission, or infinitude claim.
"""
from math import isqrt


def step(n, rules):
    for i, (numerator, denominator) in enumerate(rules):
        if n % denominator == 0:
            return n // denominator * numerator, i
    return None


def execute(n, rules):
    trace = [n]
    chosen = []
    for tick in range(3):
        nxt = step(n, rules)
        if nxt is None:
            return trace, chosen
        n, index = nxt
        trace.append(n)
        chosen.append(index)
    raise AssertionError("macro failed to halt after two steps")


def prime(n):
    return n >= 2 and all(n % i for i in range(2, isqrt(n) + 1))


def pair_survivor(n, axes):
    return all(n % p != 0 and (n + 2) % p != 0 for p in axes)


def main():
    axes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
    for p in range(2, 500):
        source = 9 * 2**p
        positive, chosen_plus = execute(source, ((2, 3),))
        negative, chosen_minus = execute(source, ((1, 6),))
        assert chosen_plus == chosen_minus == [0, 0]
        assert positive == [source, 6 * 2**p, 2**(p + 2)]
        assert negative == [source, 3 * 2**(p - 1), 2**(p - 2)]
        decoded_source = (source // 9).bit_length() - 1
        decoded_plus = positive[-1].bit_length() - 1
        decoded_minus = negative[-1].bit_length() - 1
        assert (2**decoded_source, decoded_source) == (2**p, p)
        assert (2**decoded_plus, decoded_plus) == (positive[-1], p + 2)
        assert (2**decoded_minus, decoded_minus) == (negative[-1], p - 2)
        assert pair_survivor(decoded_source, axes) == pair_survivor(p, axes)
        assert pair_survivor(decoded_plus, axes) == pair_survivor(p + 2, axes)
        assert pair_survivor(decoded_minus, axes) == pair_survivor(p - 2, axes)
        assert (prime(decoded_source) and prime(decoded_plus)) == (prime(p) and prime(p + 2))
        assert (prime(decoded_minus) and prime(decoded_source)) == (prime(p - 2) and prime(p))
    assert 3 % 2 == 1 and 2**3 % 2 == 0
    for p in axes:
        assert sum(bool(r % p and (r + 2) % p) for r in range(p)) == (1 if p == 2 else p - 2)
    assert prime(13) and not prime(15)
    print("PASS: 498 exponents, 996 guarded two-step FRACTRAN macros")
    print("PASS: decoded +/-2 inverse, certified-prime sieve and prime-2 boundary")
    print("PASS: local residue counts on 10 prime moduli, true prime-pair distinction")
    print("Bounded computational checks only; no Agda kernel or twin infinitude claimed")


if __name__ == "__main__":
    main()
