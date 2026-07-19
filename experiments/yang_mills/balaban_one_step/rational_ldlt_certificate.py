#!/usr/bin/env python3
"""Exact rational positive-definiteness certificate for a finite matrix.

Input is JSON containing a square matrix whose entries are integers or strings
accepted by fractions.Fraction, e.g. "17/8".  The script performs exact LDL^T
elimination without pivoting.  A symmetric matrix is positive definite exactly
when every resulting diagonal pivot is positive.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def parse_matrix(path: str) -> list[list[Fraction]]:
    raw = json.loads(Path(path).read_text(encoding="utf-8"))
    matrix = raw["matrix"] if isinstance(raw, dict) else raw
    A = [[Fraction(str(value)) for value in row] for row in matrix]
    n = len(A)
    if n == 0 or any(len(row) != n for row in A):
        raise ValueError("matrix must be nonempty and square")
    if any(A[i][j] != A[j][i] for i in range(n) for j in range(n)):
        raise ValueError("matrix must be exactly symmetric")
    return A


def ldlt(A: list[list[Fraction]]) -> tuple[list[list[Fraction]], list[Fraction]]:
    n = len(A)
    L = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    D = [Fraction(0) for _ in range(n)]
    for j in range(n):
        D[j] = A[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j))
        if D[j] == 0:
            raise ZeroDivisionError(f"zero LDLT pivot at {j}")
        for i in range(j + 1, n):
            L[i][j] = (
                A[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))
            ) / D[j]
    return L, D


def show(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--matrix", required=True, help="JSON rational matrix")
    ap.add_argument("--out", default="operator_analysis/rational_ldlt.json")
    args = ap.parse_args()
    A = parse_matrix(args.matrix)
    L, D = ldlt(A)
    positive = all(pivot > 0 for pivot in D)
    payload = {
        "status": "rational_certificate",
        "dimension": len(A),
        "symmetric": True,
        "positive_definite": positive,
        "pivots": [show(x) for x in D],
        "L": [[show(x) for x in row] for row in L],
        "determinant": show(__import__("functools").reduce(lambda x, y: x * y, D, Fraction(1))),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if not positive:
        raise SystemExit("matrix is not positive definite")


if __name__ == "__main__":
    main()
