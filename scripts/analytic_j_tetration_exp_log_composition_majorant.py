#!/usr/bin/env python3
"""Independent finite exact-composition checks for exp(log(1+X)) and majorant.

The infinite all-degree identities are established in
Docs/proofs/AnalyticKoenigsComplexCompositionMajorant20261110.md.
This regression is not an Agda kernel proof or a Bishop analytic identity.
"""
from fractions import Fraction as F
from math import factorial


def coefficients(degree: int, signed: bool) -> list[F]:
    """Compute exp(A(X)) via independent finite Cauchy compositions."""
    if degree < 1:
        raise ValueError("degree must be >= 1")
    power = [[F(0) for _ in range(degree + 1)] for _ in range(degree + 1)]
    power[0][0] = F(1)
    for m in range(1, degree + 1):
        for n in range(m, degree + 1):
            power[m][n] = sum(
                (F(1 if (k % 2 or not signed) else -1, k) * power[m - 1][n - k]
                 for k in range(1, n + 1)), F(0)
            )
    return [
        sum((power[m][n] / factorial(m) for m in range(n + 1)), F(0))
        for n in range(degree + 1)
    ]


def check() -> None:
    for degree in (1, 2, 4, 8, 16, 24):
        signed = coefficients(degree, signed=True)
        positive = coefficients(degree, signed=False)
        assert signed == [F(1), F(1)] + [F(0)] * (degree - 1)
        assert positive == [F(1)] * (degree + 1)
        assert all(abs(a) <= b for a, b in zip(signed, positive))
        print(f"PASS exact independent composition majorant to degree {degree}")
    for radius in (F(1, 10), F(1, 2), F(3, 4), F(9, 10)):
        for n in (0, 1, 4, 12, 40):
            tail = radius ** (n + 1) / (1 - radius)
            assert tail >= 0 and tail * (1 - radius) == radius ** (n + 1)
    print("PASS exact geometric majorant tails (formal arithmetic only)")


if __name__ == "__main__":
    check()
