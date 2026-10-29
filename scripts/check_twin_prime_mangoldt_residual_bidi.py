#!/usr/bin/env python3
"""Independent finite sanity checks for exact Mangoldt/residual transport.

Reuses classical von Mangoldt definition, tests codec fidelity only.
Original Agda owners: ResidualPhaseGeometry, RiemannVonMangoldtSpecification,
TwinPrimeNat270PeriodResidualBidiExact, ConsumerGuidedReopenableRefinementExact.
No claim of analytic correlation positivity or kernel compilation.
"""
from itertools import product
from math import isqrt, log


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def mangoldt(n: int) -> float:
    if n < 2:
        return 0.0
    for p in range(2, isqrt(n) + 2):
        if n % p == 0 and is_prime(p):
            quotient = n
            while quotient % p == 0:
                quotient //= p
            return log(p) if quotient == 1 else 0.0
    return log(n)


def encode(n: int) -> tuple[int, int]:
    if n < 0:
        raise ValueError("Natural numbers only")
    return divmod(n, 270)


def decode(code: tuple[int, int]) -> int:
    period, residue = code
    if period < 0 or not 0 <= residue < 270:
        raise ValueError("Fin 270 / Nat expected")
    return residue + 270 * period


def correlation(n: int) -> float:
    return mangoldt(n) * mangoldt(n + 2)


def main() -> dict:
    for n in range(20000):
        assert decode(encode(n)) == n
    for period, residue in product(range(80), range(270)):
        assert encode(decode((period, residue))) == (period, residue)
    for n in range(5000):
        assert mangoldt(decode(encode(n))) == mangoldt(n)
        assert correlation(decode(encode(n))) == correlation(n)
    survivors = [
        r for r in range(270)
        if all(r % p and (r + 2) % p for p in (2, 3, 5))
    ]
    assert len(survivors) == 27
    assert 59 in survivors and 209 in survivors
    assert is_prime(59) and is_prime(61)
    assert not is_prime(209) and not is_prime(329)
    assert encode(59)[1] == encode(329)[1]
    # A residue code alone is not a prime-pair correlation oracle.
    assert correlation(59) > 0
    assert correlation(329) == 0
    return {
        "status": "PASS",
        "nat_round_trips": 20000,
        "code_round_trips": 80 * 270,
        "mangoldt_cases": 5000,
        "pair_correlations": 5000,
        "wheel_survivors": 27,
        "analytic_positivity_proved": False,
    }


if __name__ == "__main__":
    print(main())
