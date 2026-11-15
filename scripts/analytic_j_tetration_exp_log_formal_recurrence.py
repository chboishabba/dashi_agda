#!/usr/bin/env python3
"""Finite exact coefficients of exp(sum_{k=1}^N (-1)^(k+1)x^k/k).

This does not prove analytic equality for original Bishop complex exp.
Formal recurrence: n*e_n=sum_{k=1}^n k*l_k*e_(n-k), e_0=1.
For 1<=n<=N, e_1=1 and e_2=...=e_N=0.
"""
from fractions import Fraction


def truncated_exp_log_coefficients(degree: int) -> list[Fraction]:
    if degree < 1:
        raise ValueError("degree must be positive")
    ell = [Fraction(0)] + [
        Fraction(1 if k % 2 else -1, k)
        for k in range(1, degree + 1)
    ]
    result = [Fraction(1)]
    for n in range(1, degree + 1):
        coefficient = sum(
            k * ell[k] * result[n-k]
            for k in range(1, n+1)
        ) / n
        result.append(coefficient)
    return result


def check() -> None:
    for degree in (1, 2, 3, 6, 12, 32, 64, 100):
        coefficients = truncated_exp_log_coefficients(degree)
        assert coefficients[0] == 1
        assert coefficients[1] == 1
        assert all(coefficient == 0 for coefficient in coefficients[2:])
        print(f"PASS exact formal exp(log(1+x)) through degree {degree}")
    print("Finite Fraction regression only: Bishop analytic equality still open.")


if __name__ == "__main__":
    check()
