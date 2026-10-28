#!/usr/bin/env python3
"""Independent exact-integer check of the typed Guy 14-rule FRACTRAN bridge.

Math/source: Conway 1987; Guy 1983 (the 15/14, 15/2 variant).
Repository owners: SignedSSPFRACTRANWeaveExact and
PrimegameSSP15CarrierFactorisationExact. New Agda priority BIDI:
PrimegameTypedNumericFirstApplicableBidiExact.
This script checks a bounded execution; it does NOT prove the
general signed SSP/FRACDASH compiler, reachability or prime infinitude.
"""
from math import prod

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)

# Exact typed SSP15 factor values, in the source rule order.
FACTORS = [
    ((17,), (7, 13)),
    ((2, 3, 13), (5, 17)),
    ((19,), (3, 17)),
    ((23,), (2, 19)),
    ((29,), (3, 11)),
    ((7, 11), (29,)),
    ((5, 19), (23,)),
    ((7, 11), (19,)),
    ((), (17,)),
    ((11,), (13,)),
    ((13,), (11,)),
    ((3, 5), (2, 7)),
    ((3, 5), (2,)),
    ((5, 11), ()),
]

# Guy (1983), NOT Conway's separate 1/7 alternative.
NUMERIC = [
    (17, 91), (78, 85), (19, 51), (23, 38),
    (29, 33), (77, 29), (95, 23), (77, 19),
    (1, 17), (11, 13), (13, 11), (15, 14),
    (15, 2), (55, 1),
]


def applicable(n, fraction):
    a, d = fraction
    return d > 0 and (n * a) % d == 0


def enabled_indices(n, program):
    return [i for i, f in enumerate(program) if applicable(n, f)]


def main():
    typed_numeric = [(prod(a), prod(d)) for a, d in FACTORS]
    assert typed_numeric == NUMERIC
    assert len(NUMERIC) == 14
    assert set(p for pair in FACTORS for side in pair for p in side) == set(PRIMES)
    n = 2
    seen = set()
    checked = 0
    for _ in range(20_000):
        typed_enabled = enabled_indices(n, typed_numeric)
        numeric_enabled = enabled_indices(n, NUMERIC)
        assert typed_enabled == numeric_enabled
        # Every rejected earlier fraction must be blocked.
        if not numeric_enabled:
            break
        i = numeric_enabled[0]
        assert all(not applicable(n, NUMERIC[j]) for j in range(i))
        a, d = NUMERIC[i]
        assert d > 0 and n * a % d == 0
        next_n = (n * a) // d
        assert next_n * d == n * a
        seen.add(i)
        checked += 1
        n = next_n
    assert seen == set(range(14))
    print(f"PASS: {len(NUMERIC)} original Guy rules, {len(PRIMES)} factors, "
          f"{checked} selected exact steps; all rule-prefix guards agree")
    print("Theorem level: executed finite Python only; Agda kernel pending")


if __name__ == "__main__":
    main()
