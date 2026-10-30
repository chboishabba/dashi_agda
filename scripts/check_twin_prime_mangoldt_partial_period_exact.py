#!/usr/bin/env python3
"""Independent, exact symbolic M13 arbitrary-partial/full-period BIDI checks.

Symbolic Lambda(n)Lambda(n+2) is represented by basis monomial
log(p)log(q), with no floating-point rounding. This does not prove
the analytic correlation lower bound or compile Agda. 2026-10-30.

Attribution: classical von Mangoldt; reused DASHI original owners:
RiemannVonMangoldtSpecification, RiemannPrimePowerCounting,
TwinPrimeNat270PeriodResidualBidiExact, MangoldtMultiPeriodConcatExact.
"""
from functools import lru_cache
from collections import Counter
from math import isqrt

@lru_cache(maxsize=None)
def prime_power_base(n):
    if n < 2:
        return None
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            q = n
            while q % p == 0:
                q //= p
            return p if q == 1 else None
    return n

def mangoldt_pair_basis(n):
    p, q = prime_power_base(n), prime_power_base(n + 2)
    return (p, q) if p is not None and q is not None else None

def main():
    checks = 0
    symbolic = 0
    starts = list(range(0, 800, 11)) + [59, 209, 329, 270, 540, 810, 10001]
    for start in starts:
        period = (start + 269) // 270
        prefix = 270 * period - start
        assert start + prefix == 270 * period
        for blocks in (0, 1, 2, 5):
            for suffix in (0, 1, 11, 269):
                length = prefix + 270 * blocks + suffix
                ordinary = list(range(start, start + length))
                reconstructed = list(range(start, start + prefix))
                for k in range(period, period + blocks):
                    reconstructed.extend(270 * k + r for r in range(270))
                reconstructed.extend(
                    range(270 * (period + blocks),
                          270 * (period + blocks) + suffix))
                assert ordinary == reconstructed
                if checks % 7 == 0:
                    first = Counter(w for n in ordinary
                                    if (w := mangoldt_pair_basis(n)) is not None)
                    second = Counter(w for n in reconstructed
                                     if (w := mangoldt_pair_basis(n)) is not None)
                    assert first == second
                    symbolic += 1
                checks += 1
    for k in range(75):
        for r in range(270):
            assert divmod(270 * k + r, 270) == (k, r)
    assert mangoldt_pair_basis(59) == (59, 61)
    assert mangoldt_pair_basis(209) is None
    assert mangoldt_pair_basis(329) is None
    print({'status': 'PASS', 'aligned_partial_period_cases': checks,
           'exact_symbolic_pair_sum_checks': symbolic,
           'period_residue_round_trips': 75 * 270,
           'counterexample_checks': 3,
           'kernel_checked': False, 'analytic_positivity_proved': False})

if __name__ == '__main__':
    main()
