#!/usr/bin/env python3
"""Exact finite checks for the September 2026 non-Archimedean spectral paper.

Upstream mathematical source:
Research Group for Spectral Geometry and Theoretical Computing,
sneed-and-feed/adelic-spectral-zeta,
papers/nonarchimedean_spectral_dynamics.md (September 2026).

DASHI already owns the formal proof/counterexample route in PR #703 and
DASHI/Analysis/NonArchimedean*. This is an independently executable
small-N INTEGER regression, not a new Lean or Agda kernel theorem.
"""

from __future__ import annotations


def multiply(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    n = len(a)
    result = [[0] * n for _ in range(n)]
    for i in range(n):
        for k, value in enumerate(a[i]):
            if value:
                for j, other in enumerate(b[k]):
                    result[i][j] += value * other
    return result


def matrix_power(a: list[list[int]], exponent: int) -> list[list[int]]:
    n = len(a)
    result = [[int(i == j) for j in range(n)] for i in range(n)]
    while exponent:
        if exponent & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        exponent >>= 1
    return result


def trace(a: list[list[int]]) -> int:
    return sum(row[i] for i, row in enumerate(a))


def twisted_sheet_block(n: int) -> list[list[int]]:
    """Compute the actual tau-odd spatial block, not an assumed Fourier block.

    The sheet involution is x -> x + 2^(n-1) on Z/(2^n).
    The tau-odd extension has f(x + M) = -f(x).
    Df(x) = f(3x) + f(3x-1), indices modulo 2^n.
    """
    if n < 2:
        raise ValueError("twisted sheet comparison starts at n=2")
    modulus = 1 << n
    half = modulus >> 1
    block = [[0] * half for _ in range(half)]
    for x in range(half):
        for y in ((3 * x) % modulus, (3 * x - 1) % modulus):
            block[x][y % half] += 1 if y < half else -1
    return block


def check_small_levels() -> None:
    for n in range(2, 7):
        half = 1 << (n - 1)
        first_return = 1 << (n - 2)
        block = twisted_sheet_block(n)
        for power in range(1, first_return + 1):
            assert trace(matrix_power(block, power)) == 0, (n, power)

        doubled = matrix_power(block, 2 * first_return)
        # n=2 is an explicit EXCEPTION to the n>=3 minus-two theorem.
        scalar = 2 if n == 2 else -2
        expected = [[scalar * int(i == j) for j in range(half)]
                    for i in range(half)]
        assert doubled == expected, f"n={n}: wrong twisted matrix power"
        if n >= 3:
            assert trace(doubled) == -(1 << n), f"n={n}: wrong doubled trace"
        print(f"n={n}: trace(S^m)=0 for 1<=m<={first_return}; "
              f"S^{2 * first_return}={scalar}I")

    # Reuse the pre-existing exact n=3 mixing counterexample from DASHI.
    v = [-1, -1, -1, 0, 1, 1, 1, 0]
    dv = [v[(3 * x) % 8] + v[(3 * x - 1) % 8] for x in range(8)]
    assert sum(x * x for x in v) == 6
    assert sum(x * x for x in dv) == 20
    # P = D/2, so ||Pv||^2 = 5 > 3 = (1/2)||v||^2.
    assert sum(x * x for x in dv) > 2 * sum(x * x for x in v)
    print("n=3: existing unit-prefactor one-step L2 counterexample confirmed")

    # Reuse the existing n=3 set A={4}, start 1 survival counterexample.
    paths = [(1,)]
    for _ in range(3):
        paths = [p + (y,) for p in paths
                 for y in ((3 * p[-1]) % 8, (3 * p[-1] - 1) % 8)
                 if y != 4]
    assert len(paths) == 8
    print("n=3: all 8 length-three branch words avoid stopping set {4}")
    print("PASS: finite integer checks only; no general kernel claim")


if __name__ == "__main__":
    check_small_levels()
