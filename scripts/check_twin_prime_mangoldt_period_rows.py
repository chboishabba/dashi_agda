#!/usr/bin/env python3
"""Exact arithmetic oracle for M13 Fin270 period rows, original PR #1408.

This checks BIDI and finite sum/indexing identity, never positivity.
Sources: classical Euclidean division and von Mangoldt; reused DASHI
TwinPrimeNat270PeriodResidualBidiExact and the pre-existing Mangoldt owner.
"""
from math import fsum, isqrt, log

def mangoldt(n: int) -> float:
    if n < 2:
        return 0.0
    for prime in range(2, isqrt(n) + 1):
        if n % prime == 0:
            quotient = n
            while quotient % prime == 0:
                quotient //= prime
            return log(prime) if quotient == 1 else 0.0
    return log(n)

def pair(n: int) -> float:
    return mangoldt(n) * mangoldt(n + 2)

def encode(n: int) -> tuple[int, int]:
    assert n >= 0
    return divmod(n, 270)

def decode(code: tuple[int, int]) -> int:
    k, r = code
    assert k >= 0 and 0 <= r < 270
    return r + 270 * k

def interval_partition(start: int, count: int) -> list[int]:
    assert start >= 0 and count >= 0
    if not count:
        return []
    return [
        decode((k, r))
        for k in range(start // 270, (start + count - 1) // 270 + 1)
        for r in range(270)
        if start <= decode((k, r)) < start + count
    ]

def main() -> dict:
    for period in range(80):
        row = [decode((period, r)) for r in range(270)]
        assert row == list(range(period * 270, (period + 1) * 270))
        assert all(encode(n) == (period, r) for r, n in enumerate(row))
        assert fsum(pair(n) for n in row) == fsum(
            pair(decode((period, r))) for r in range(270))
    checks = 0
    for start in (0, 1, 59, 209, 269, 270, 271, 329, 539, 540, 541, 1001):
        for count in (0, 1, 2, 10, 270, 271, 539):
            xs = list(range(start, start + count))
            ys = interval_partition(start, count)
            assert xs == ys
            assert fsum(pair(n) for n in xs) == fsum(pair(n) for n in ys)
            checks += 1
    for n in range(20000):
        assert decode(encode(n)) == n
    return {
        "status": "PASS",
        "complete_period_rows": 80,
        "partial_interval_partitions": checks,
        "period_inverse_witnesses": 80 * 270,
        "nat_inverse_witnesses": 20000,
        "analytic_positivity_proved": False,
    }

if __name__ == "__main__":
    print(main())
