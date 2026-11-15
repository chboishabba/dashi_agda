#!/usr/bin/env python3
"""Exact finite jets for the exponential Schroeder conjugacy.

At a selected fixed point exp(a)=a, the displaced exponential germ is
lambda*(exp(t)-1), lambda=a. The formal linearization chi(t)=t+sum c_n t^n
satisfies chi(lambda*(exp(t)-1))=lambda*chi(t) coefficientwise.

A finite exact jet is NOT a holomorphic/convergent Kneser construction.
The recurrence requires lambda^(n-1) != 1 for every n >=2.
"""
import argparse
import sympy as sp


def coefficients(degree):
    if degree < 2:
        raise ValueError("degree must be >= 2")
    t, lam = sp.symbols("t lambda")
    germ = lam * sum(t**j / sp.factorial(j)
                     for j in range(1, degree + 1))
    powers = [sp.Integer(1)]
    for _ in range(1, degree + 1):
        powers.append(sp.expand(powers[-1] * germ))
    cs = {1: sp.Integer(1)}
    for n in range(2, degree + 1):
        known = sum(cs[k] * powers[k].coeff(t, n)
                    for k in range(1, n))
        cs[n] = sp.cancel(-known / (lam**n - lam))
    residual = [
        sp.factor(sum(cs[k] * powers[k].coeff(t, n)
                      for k in range(1, n + 1)) - lam * cs[n])
        for n in range(1, degree + 1)
    ]
    assert all(value == 0 for value in residual), residual
    assert sp.factor(cs[2] + 1 / (2 * (lam - 1))) == 0
    assert sp.factor(
        cs[3] - (2 * lam + 1) /
        (6 * (lam - 1)**2 * (lam + 1))
    ) == 0
    return cs, residual


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=6)
    args = parser.parse_args()
    coeffs, residuals = coefficients(args.degree)
    print("Exact symbolic Schroeder residuals:", residuals)
    for n in sorted(coeffs):
        print("c_%d =" % n, sp.factor(coeffs[n]))
    print("PASS: formal coefficients vanish through degree", args.degree)
