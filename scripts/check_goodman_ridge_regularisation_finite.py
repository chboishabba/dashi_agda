#!/usr/bin/env python3
"""Synthetic exact-rational ridge diagnostic; NOT acoustic data or Agda proof.

Inspired by independent work on noise-aware regularisation in acoustics:
Coletti, Davis & Schultz (2025), DOI 10.1016/j.apacoust.2025.110756.
The algebra, fixtures, and regression in this file are newly authored here.
"""
from fractions import Fraction as Q
from json import dumps


def second_coordinate(q, rho, a, b):
    return rho * q * (b - a)


def run():
    rows = []
    checks = 0
    for n in (1, 2, 10, 100, 1000, 10000):
        q, x, y = Q(1, n), Q(2, 3), Q(5, 7)
        for label, lam in (('none', Q(0)), ('squared-gain', q*q), ('gain', q)):
            rho = 1 / (q*q + lam)
            bias = -(rho*lam)*y
            gain = rho*q
            assert rho*(q*q+lam) == 1
            assert (rho*q*q)*y + (rho*lam)*y == y
            assert gain <= 1/q
            for first, second in (
                (q, Q(0)), (Q(0), q), (q, q), (q, -q)
            ):
                a, b = x + first, x + q*y + second
                recovered = second_coordinate(q, rho, a, b)
                assert (q*q + lam)*recovered == q*(b-a)
                assert recovered - y == bias + gain*(second-first)
                assert recovered == (rho*q*q)*y + gain*(second-first)
                if first == second:
                    assert recovered-y == bias
                checks += 1
            rows.append({
                'n': n, 'lambda_kind': label, 'lambda': str(lam),
                'noise_gain': str(gain), 'noise_free_bias': str(bias),
                'conditional_inverse_coefficient': str(rho)
            })
    assert checks == 72
    assert len(rows) == 18
    print(dumps({
        'mode': 'synthetic-exact-rational', 'all_passed': True,
        'tests': checks, 'parameter_rows': rows,
        'boundary': 'Regularization trades noise amplification for bias; no lambda selection or acoustic evidence',
        'not_checked': ['Agda kernel', 'real microphone', 'causal outcome', 'Monster same-object']
    }, indent=2))
    return rows


if __name__ == '__main__':
    run()
