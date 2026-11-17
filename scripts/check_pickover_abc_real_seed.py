#!/usr/bin/env python3
"""Machin-exact analytic seed into 3x3/27 ternary ABC action.

Reuse scripts/check_pickover_machin_factorial_phase.py exact pi bounds.
Six small factorial signs are independently anchored to real sin by
floor(99^(n!)/pi) parity. No claim for 9999! or fast pi digits.
"""
from fractions import Fraction
from math import factorial
from itertools import permutations
from check_pickover_machin_factorial_phase import interval_pi

def floor(q):
    return q.numerator // q.denominator

def digits3(p, n):
    result = [0] * n
    for j in range(n - 1, -1, -1):
        result[j], p = p % 3, p // 3
    assert p == 0
    return result

def circle(x):
    return x % 1

def audit_factorial(n):
    exponent = factorial(n)
    argument = 99 ** exponent
    decimals = 2 * exponent + 45
    scale = 10 ** decimals
    pi_lo, pi_hi = interval_pi(scale)
    assert 0 < pi_lo < pi_hi
    lo = Fraction(argument * scale, 2 * pi_hi)
    hi = Fraction(argument * scale, 2 * pi_lo)
    winding = floor(lo)
    assert winding == floor(hi)
    xlo, xhi = lo - winding, hi - winding
    assert 0 < xlo <= xhi < 1
    address = floor(27 * xlo)
    assert address == floor(27 * xhi)
    abc = digits3(address, 3)
    tail_lo, tail_hi = 27 * xlo - address, 27 * xhi - address
    assert 0 < tail_lo <= tail_hi < 1

    certified_sign, first_depth = None, None
    for depth in range(1, 20):
        a, b = floor(3 ** depth * xlo), floor(3 ** depth * xhi)
        if a != b: continue
        trits = digits3(a, depth)
        differing = [v for v in trits if v != 1]
        if differing:
            certified_sign = +1 if differing[0] == 0 else -1
            first_depth = depth
            break
    assert certified_sign is not None
    direct_lo = floor(Fraction(argument * scale, pi_hi))
    direct_hi = floor(Fraction(argument * scale, pi_lo))
    assert direct_lo == direct_hi
    assert certified_sign == (+1 if direct_lo % 2 == 0 else -1)

    for sigma in permutations(range(3)):
        changed = [abc[i] for i in sigma]
        shifted = 9 * changed[0] + 3 * changed[1] + changed[2]
        delta = Fraction(shifted - address, 27)
        correction = circle(99 * delta)
        assert correction in (0, Fraction(1, 3), Fraction(2, 3))
        for endpoint in (xlo, xhi):
            assert circle(99 * (endpoint + delta)) == circle(99 * endpoint + correction)
    print("n", n, "E", exponent, "ABC", abc, "sign", certified_sign,
          "first-noncentral-depth", first_depth, "pi-digits", decimals)
    return tuple(abc), certified_sign

def main():
    expected = [((2,0,2),-1),((2,1,2),-1),((0,0,1),1),
                ((0,2,2),1),((2,2,2),-1),((0,1,2),1)]
    assert [audit_factorial(n) for n in range(1,7)] == expected
    print("PASS: six actual factorial pi-phase certificates with ABC S3/C3 corrections")
    print("OPEN: cheap terminal seed tail producer for 99^(9999!)")

if __name__ == "__main__":
    main()
