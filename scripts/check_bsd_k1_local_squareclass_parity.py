#!/usr/bin/env python3
"""Exact rational/p-adic local arithmetic regression for ORIGINAL E:y²=x³-x.

The local Q_p-square criterion is a classical theorem; this Python script
checks arithmetic instances and deliberate negative controls only.
It does NOT construct E(Q_p), E[2]-valued H¹ or the Selmer comparison.
The actual Agda integer case split is in:
  EllipticCubicValuationParityExact
  EllipticOddPrimeSecondValuationParityExact

For p=2, a nonzero rational is a Q2 square iff v2 is even and its odd
unit residue is 1 mod 8. For odd p, iff v_p is even and the residual
unit is a nonzero quadratic residue mod p. Numerator and denominator
are handled exactly; this is not floating point or random sampling.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd

PRIMES = (2, 3, 5, 7, 11, 13)
CURVE = "y^2=x(x-1)(x+1)"


def valuation_integer(n: int, p: int) -> int:
    if n == 0:
        raise ValueError("valuation of zero is infinite")
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def valuation(q: Fraction, p: int) -> int:
    if q == 0:
        raise ValueError("valuation of zero is infinite")
    return valuation_integer(q.numerator, p) - valuation_integer(q.denominator, p)


def square_in_Qp(q: Fraction, p: int) -> bool:
    if q == 0:
        return True
    if p not in PRIMES:
        raise ValueError("p must be one of the audited primes")
    v = valuation(q, p)
    if v % 2 != 0:
        return False
    num = q.numerator // p**valuation_integer(q.numerator, p)
    den = q.denominator // p**valuation_integer(q.denominator, p)
    if p == 2:
        return (num * pow(den, -1, 8)) % 8 == 1
    unit = num * pow(den, -1, p) % p
    return pow(unit, (p - 1) // 2, p) == 1


def curve_rhs(x: Fraction) -> Fraction:
    return x * (x - 1) * (x + 1)


def assess(max_numerator: int = 100, max_denominator: int = 30) -> dict:
    counts: dict[str, int] = {}
    witnesses: dict[str, str] = {}
    for p in PRIMES:
        total = 0
        for den in range(1, max_denominator + 1):
            for num in range(-max_numerator, max_numerator + 1):
                if num in (0, den, -den) or gcd(abs(num), den) != 1:
                    continue
                x = Fraction(num, den)
                if not square_in_Qp(curve_rhs(x), p):
                    continue
                total += 1
                assert valuation(x, p) % 2 == 0, (p, x, "first Kummer parity")
                if p != 2:
                    assert valuation(x - 1, p) % 2 == 0, (
                        p, x, "odd-prime second Kummer parity")
                if str(p) not in witnesses:
                    witnesses[str(p)] = str(x)
        counts[str(p)] = total

    # Strong negative control: x=39 actually admits y in Q2 (by the
    # genuine odd-unit-square criterion), but v2(x-1)=v2(38)=1.
    # Thus the second coordinate is NOT even at p=2.
    x = Fraction(39)
    rhs = curve_rhs(x)
    assert rhs == 59280
    assert valuation(rhs, 2) == 4
    assert (rhs / 16).numerator % 8 == 1  # 3705 == 1 mod 8
    assert square_in_Qp(rhs, 2)
    assert valuation(x, 2) == 0
    assert valuation(x - 1, 2) == 1

    # A parity-compatible rational RHS need not be a Q2 square:
    # 336 = 16*21 has even v2 but unit 21 = 5 mod 8.
    not_square = curve_rhs(Fraction(7))
    assert valuation(not_square, 2) == 4
    assert not square_in_Qp(not_square, 2)
    return {
        "curve": CURVE,
        "audited_primes": list(PRIMES),
        "rational_x_range": {
            "numerator_abs_le": max_numerator,
            "denominator_le": max_denominator},
        "actual_local_square_criterion_mathematical_reference": True,
        "local_square_tested_nonexceptional_x_counts": counts,
        "sample_x": witnesses,
        "first_coordinate_even_at_every_tested_prime": True,
        "second_coordinate_even_at_all_tested_odd_primes": True,
        "Q2_second_parity_false_actual_point": {
            "x": 39, "y_squared": 59280,
            "v2_x_minus_one": 1,
            "Q2_square_witness_criterion": "59280=2^4*3705; 3705 mod 8=1"},
        "negative_control_even_valuation_not_sufficient": {
            "x": 7, "y_squared": 336, "unit_mod_8": 5},
        "agda_kernel_accepted": False,
        "Qp_point_and_H1_localization_constructed_in_Agda": False,
        "classical_Sha2_identified": False,
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--max-numerator", type=int, default=100)
    p.add_argument("--max-denominator", type=int, default=30)
    args = p.parse_args()
    if args.max_numerator < 2 or args.max_denominator < 1:
        raise SystemExit("need nontrivial positive enumeration bounds")
    print(json.dumps(assess(args.max_numerator, args.max_denominator),
                     indent=2))


if __name__ == "__main__":
    main()
