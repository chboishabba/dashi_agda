#!/usr/bin/env python3
"""Independent nonnegative ten-plane dimensional BIDI reference check.

Matches the finite Nat-valued arithmetic in
DASHI/Physics/YangMills/YMClayFiveSectorBidiSteelmanExact.agda.

This checks plaquette accounting and missing-fibre obstructions; it is not
a gauge/KK action, Haar/OS proof, or Agda kernel acceptance.
"""
from __future__ import annotations
import itertools
import random
from fractions import Fraction

KEYS = ("01", "02", "03", "04", "12", "13", "14", "23", "24", "34")

def dimensional_plane_sums(w: dict[str, int]) -> tuple[int, ...]:
    assert set(w) == set(KEYS)
    assert all(isinstance(x, int) and x >= 0 for x in w.values())
    p2 = w["01"]
    c3 = w["02"] + w["12"]
    p3 = p2 + c3
    c4 = w["03"] + w["13"] + w["23"]
    p4 = p3 + c4
    c5 = w["04"] + w["14"] + w["24"] + w["34"]
    p5 = p4 + c5
    return p2, p3, p4, p5, c3, c4, c5

def check_assignment(w: dict[str, int]) -> None:
    p2, p3, p4, p5, c3, c4, c5 = dimensional_plane_sums(w)
    assert p3 == p2 + c3
    assert p4 == p3 + c4
    assert p5 == p4 + c5
    assert (p3 == p2) == (c3 == 0)
    assert (p4 == p3) == (c4 == 0)
    assert (p5 == p4) == (c5 == 0)

def main() -> None:
    for key in KEYS:
        state = {name: int(name == key) for name in KEYS}
        check_assignment(state)
    # Exact exhaustive small nonnegative assignments:
    for coeffs in itertools.product(range(2), repeat=len(KEYS)):
        check_assignment(dict(zip(KEYS, coeffs)))
    # Reproduces independent larger-value reference selection.
    rng = random.Random(369)
    for _ in range(100_000):
        check_assignment({name: rng.randrange(20) for name in KEYS})
    example = {name: int(name == "04") for name in KEYS}
    assert dimensional_plane_sums(example) == (0, 0, 0, 1, 0, 0, 1)
    # Algebraic circumference factors for conditional tree-level zero modes.
    # No physical threshold, SI unit, or compactification claim follows.
    for _ in range(100_000):
        l3 = Fraction(rng.randint(1, 30), rng.randint(1, 30))
        l4 = Fraction(rng.randint(1, 30), rng.randint(1, 30))
        l5 = Fraction(rng.randint(1, 30), rng.randint(1, 30))
        inverse_g5_squared = Fraction(rng.randint(1, 30), rng.randint(1, 30))
        assert l3 * (l4 * (l5 * inverse_g5_squared)) == (
            (l3 * l4) * l5
        ) * inverse_g5_squared
    print("PASS: 10 one-plane + 1024 exhaustive binary + 100000 seeded BIDI assignments")
    print("PASS: 5D cross-fibre nonzero while 4D projection is zero")
    print("PASS: 100000 positive rational inverse-coupling product matches")

if __name__ == "__main__":
    main()
