#!/usr/bin/env python3
"""Exact independent formal EXP∘LOG and EXP∘ATAN coefficient regression.

This uses the *actual original* rational formal coefficient streams:
    -L(X) = -sum_(k>=1) X^k/k,
    2i*A(X) = sum_(m>=0) 2i*(-1)^m * X^(2m+1)/(2m+1).
It computes the formal exponential coefficients by the universal
chain-rule recurrence n*b_n = sum_(k=1)^n k*c_k*b_(n-k).
It does NOT insert the claimed answer as the recurrence input.

All arithmetic is exact Fraction Q[i], no floats; this is a
non-promotional independent regression, NOT Agda/Bishop convergence.
"""
import argparse
from fractions import Fraction as F


ZERO = (F(0), F(0))
ONE = (F(1), F(0))
I = (F(0), F(1))


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0]


def exp_coefficients(n_max, weighted_source_coeff):
    a = [ONE]
    for n in range(1, n_max + 1):
        summed = ZERO
        for k in range(1, n + 1):
            w = weighted_source_coeff(k)
            if w != ZERO:
                summed = add(summed, mul(w, a[n-k]))
        a.append((summed[0]/n, summed[1]/n))
    return a


def weighted_negative_log(k):
    # k times original coefficient -1/k
    return (F(-1), F(0))


def weighted_double_i_atan(k):
    # k times original coefficient: 2i*(-1)^((k-1)/2) at odd k
    if k % 2 == 0:
        return ZERO
    return F(0), F(2*(-1)**((k-1)//2))


def gaussian_i_power(n):
    k = n % 4
    return (ONE, I, (F(-1), F(0)), (F(0), F(-1)))[k]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--through-degree", type=int, default=96)
    opts = ap.parse_args()
    if not 2 <= opts.through_degree <= 1000:
        raise SystemExit("out-of-range through-degree")
    log_coeff = exp_coefficients(opts.through_degree, weighted_negative_log)
    atan_coeff = exp_coefficients(opts.through_degree, weighted_double_i_atan)
    for n in range(opts.through_degree + 1):
        expected_log = ONE if n == 0 else (F(-1), F(0)) if n == 1 else ZERO
        expected_atan = ONE if n == 0 else mul((F(2), F(0)), gaussian_i_power(n))
        assert log_coeff[n] == expected_log, ("LOG", n, log_coeff[n])
        assert atan_coeff[n] == expected_atan, ("ATAN", n, atan_coeff[n])
    print(f"PASS: original -L and 2i*atan formal-exp source coefficients, degrees 0..{opts.through_degree}")
    print("LOG formal EXP coefficients: [1,-1,0,0,...]")
    print("ATAN formal EXP coefficients: [1,2i,-2,-2i,2,2i,...]")
    print("NON-PROMOTIONAL: analytic Bishop absolute composition/limit transport and Agda kernel acceptance remain separate.")


if __name__ == "__main__":
    main()
