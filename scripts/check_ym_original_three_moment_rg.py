#!/usr/bin/env python3
"""Exact-rational regression for original Wilson R445 three-moment error algebra.

An exhaustive bounded integer grid tests the *scalar inequality* and
covariance subtraction normalization. This neither proves original
physical Wilson RG moment bounds nor substitutes for an Agda kernel receipt.
"""
from fractions import Fraction
from itertools import product


def covariance(left, right, pair):
    return pair - left * right


def check():
    values = tuple(Fraction(x) for x in (-2, -1, 0, 1, 2))
    cases = exact_cases = 0
    for e_l, b_l, e_r, b_r, e_pair, b_pair in product(values, repeat=6):
        eps_l = abs(e_l - b_l)
        eps_r = abs(e_r - b_r)
        eps_pair = abs(e_pair - b_pair)
        bound = eps_pair + eps_l * abs(e_r) + abs(b_l) * eps_r
        lhs = abs(covariance(e_l, e_r, e_pair) - covariance(b_l, b_r, b_pair))
        residual = abs((e_pair - b_pair) - (e_l * e_r - b_l * b_r))
        assert lhs == residual, (lhs, residual)
        assert lhs <= bound, (lhs, bound)
        if e_l == b_l and e_r == b_r and e_pair == b_pair:
            assert lhs == 0
            exact_cases += 1
        cases += 1

    # Algebraic negative control, NOT an actual Wilson SU(N) realization:
    # distinct source moments cannot be silently identified by blocking.
    assert covariance(Fraction(1), Fraction(1), Fraction(0)) != covariance(
        Fraction(0), Fraction(0), Fraction(0))
    print(f"PASS: {cases} exact rational six-moment cases, {exact_cases} equality cases, RG nonclosure negative control")


if __name__ == "__main__":
    check()
