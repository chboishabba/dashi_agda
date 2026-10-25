#!/usr/bin/env python3
"""Fast factorial jump: symbolic cost versus certified phase information.
Uses only exact integers/fractions. Source contribution: DASHI audit.
"""
from fractions import Fraction
from math import factorial

def interval_power_circle(lo, hi, m):
    width = (hi - lo) * m
    if width >= 1:
        return None
    l, h = m * lo, m * hi
    a, b = l.numerator // l.denominator, h.numerator // h.denominator
    return None if a != b else (l - a, h - b)

def signed_chamber(interval):
    if interval is None:
        return None
    a, b = interval
    if 0 < a <= b < Fraction(1, 2):
        return +1
    if Fraction(1, 2) < a <= b < 1:
        return -1
    return None

def main():
    print("n | bits(n!) | binary squarings | selected powers")
    for n in (5,6,7,8,10,20,100,1000,9999):
        k = factorial(n)
        print(n, k.bit_length(), k.bit_length()-1, k.bit_count())
    m = 10**6
    # Same coarse phase interval, different terminal signs.
    a, b = Fraction(1,8*m), Fraction(5,8*m)
    assert signed_chamber(interval_power_circle(a,a,m)) == 1
    assert signed_chamber(interval_power_circle(b,b,m)) == -1
    assert signed_chamber(interval_power_circle(a,b,m)) is None
    # A power map F_b^k is exact and succinct, but interval error
    # is multiplied by b^k. No claim about special pi input follows.
    assert factorial(9999).bit_length() == 118445
    print("PASS: jump description logarithmic in exponent; coarse phase loses sign")
    print("OPEN: exceptional real-phase certificate for 99^(9999!)")

if __name__ == "__main__":
    main()
