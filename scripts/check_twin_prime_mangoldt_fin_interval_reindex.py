#!/usr/bin/env python3
"""Independent arithmetic oracle for M13 complete Fin270 interval reindexing.

Test ordered row equivalence and boundary partitions, not analytic positivity.
Owners: DASHI NatPeriod270, MangoldtFiniteSumBidi and PeriodRowsExact.
"""
from math import isqrt, log

def mangoldt(n):
    if n < 2: return 0.0
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return log(p) if m == 1 else 0.0
    return log(n)

def pair(n): return mangoldt(n) * mangoldt(n + 2)

def main():
    for k in range(55):
        finite_row = [pair(270 * k + r) for r in range(270)]
        numeric_interval = [pair(n) for n in range(270 * k, 270 * (k + 1))]
        assert finite_row == numeric_interval
        for r in range(270):
            assert divmod(270 * k + r, 270) == (k, r)
    checks = 0
    for start in (0, 1, 59, 209, 269, 270, 329, 539, 1001, 10438):
        for size in (0, 1, 2, 17, 269, 270, 271, 540):
            direct = list(range(start, start + size))
            partition = [] if size == 0 else [
                270 * k + r
                for k in range(start // 270, (start + size - 1) // 270 + 1)
                for r in range(270)
                if start <= 270 * k + r < start + size
            ]
            assert direct == partition
            assert [pair(n) for n in direct] == [pair(n) for n in partition]
            checks += 1
    return {"status": "PASS", "complete_rows": 55, "cross_period_intervals": checks,
            "period_residue_witnesses": 55 * 270,
            "agda_kernel_verified": False, "analytic_positivity_proved": False}

if __name__ == "__main__":
    print(main())
