#!/usr/bin/env python3
"""Exact rational interval LDLT positivity certificate.

Input JSON is a square symmetric matrix whose entries are either exact values
or [lower, upper] rational intervals. All arithmetic is performed with
fractions.Fraction, so the resulting enclosure has no floating roundoff. The
certificate succeeds only when every interval pivot has a strictly positive
lower endpoint.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("empty interval")

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        values = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(values), max(values))

    def reciprocal(self) -> "Interval":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval contains zero")
        values = (Fraction(1, 1) / self.lo, Fraction(1, 1) / self.hi)
        return Interval(min(values), max(values))

    def __truediv__(self, other: "Interval") -> "Interval":
        return self * other.reciprocal()


ZERO = Interval(Fraction(0), Fraction(0))
ONE = Interval(Fraction(1), Fraction(1))


def fraction(value: object) -> Fraction:
    return Fraction(str(value))


def interval(value: object) -> Interval:
    if isinstance(value, list):
        if len(value) != 2:
            raise ValueError("interval entries require [lo, hi]")
        return Interval(fraction(value[0]), fraction(value[1]))
    return Interval(fraction(value), fraction(value))


def load_matrix(path: str) -> list[list[Interval]]:
    raw = json.loads(Path(path).read_text(encoding="utf-8"))
    matrix = raw["matrix"] if isinstance(raw, dict) else raw
    A = [[interval(value) for value in row] for row in matrix]
    n = len(A)
    if n == 0 or any(len(row) != n for row in A):
        raise ValueError("matrix must be nonempty and square")
    for i in range(n):
        for j in range(n):
            if A[i][j] != A[j][i]:
                raise ValueError("interval matrix must be exactly symmetric")
    return A


def sum_intervals(values) -> Interval:
    total = ZERO
    for value in values:
        total = total + value
    return total


def ldlt(A: list[list[Interval]]) -> tuple[list[list[Interval]], list[Interval]]:
    n = len(A)
    L = [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]
    D = [ZERO for _ in range(n)]
    for j in range(n):
        correction = sum_intervals(L[j][k] * L[j][k] * D[k] for k in range(j))
        D[j] = A[j][j] - correction
        if D[j].lo <= 0:
            raise ArithmeticError(
                f"pivot {j} not certified positive: [{D[j].lo}, {D[j].hi}]"
            )
        for i in range(j + 1, n):
            numerator = A[i][j] - sum_intervals(
                L[i][k] * L[j][k] * D[k] for k in range(j)
            )
            L[i][j] = numerator / D[j]
    return L, D


def show_fraction(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def show_interval(value: Interval) -> list[str]:
    return [show_fraction(value.lo), show_fraction(value.hi)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix", required=True)
    parser.add_argument("--out", default="operator_analysis/interval_ldlt.json")
    args = parser.parse_args()
    A = load_matrix(args.matrix)
    L, D = ldlt(A)
    determinant = ONE
    for pivot in D:
        determinant = determinant * pivot
    payload = {
        "status": "interval_certificate",
        "dimension": len(A),
        "positive_definite": True,
        "pivots": [show_interval(value) for value in D],
        "determinant_interval": show_interval(determinant),
        "L": [[show_interval(value) for value in row] for row in L],
    }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
