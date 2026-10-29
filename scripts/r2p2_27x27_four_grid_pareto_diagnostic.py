#!/usr/bin/env python3
"""4³ versus 5³ padded MODE-INDEX quadratic convolution Pareto audit.

Reuses the existing canonical 27 cube and 729 ordered pair enumerator.
The sampled-frequency mathematical prior art is Patterson/Orszag and
Lambert/Reneuve/Augier (arXiv:2603.08892, March 2026).

This is exact finite group-index aggregation, NOT an FFT implementation.
The 4-point cyclic index quotient merges ±2, but those outputs are NOT
retained when projecting onto {-1,0,+1}. Five-point indexing preserves
all five signed sum modes. Three-point folds +2 onto -1 spuriously.
"""
from __future__ import annotations

from fractions import Fraction
from collections import defaultdict
import json

from r2p2_27x27_incidence_convolution_diagnostic import (
    CUBE27, PAIRS729, WIDE125, integer_sum,
)

RETAINED = set(CUBE27)


def fold(n: int, grid: int) -> int:
    """Return a canonical frequency class for a 3/4/5-point grid."""
    if grid not in (3, 4, 5):
        raise ValueError("supported grids are N=3,4,5")
    return (n + grid // 2) % grid - grid // 2


def fold_cube(mode, grid):
    return tuple(fold(n, grid) for n in mode)


def convolution_pair_bilinear(left, right, grid=None):
    coefficients = defaultdict(int)
    for p, q in PAIRS729:
        if grid:
            # Genuine cyclic group operation on the encoded inputs,
            # rather than calculating the Z³ sum and relabelling it.
            k = tuple(fold(fold(a, grid) + fold(b, grid), grid)
                      for a, b in zip(p, q))
        else:
            k = integer_sum(p, q)
        coefficients[k] += left[p] * right[q]
    return coefficients


def check_finite_index_pareto():
    """Exact rational and integer profiles, including negative coefficients."""
    profiles = []
    for case in range(6):
        if case == 0:
            left = {k: Fraction(0) for k in CUBE27}
            right = {k: Fraction(1) for k in CUBE27}
        elif case == 1:
            left = {k: Fraction(1) for k in CUBE27}
            right = {k: Fraction(1) for k in CUBE27}
        elif case == 2:
            left = {k: Fraction(2 * k[0] - 3 * k[1] + k[2], 7) for k in CUBE27}
            right = {k: Fraction(3 * k[0] + k[1] - 2 * k[2], 5) for k in CUBE27}
        elif case == 3:
            left = {k: Fraction(int(k == (1, 0, 0))) for k in CUBE27}
            right = dict(left)
        elif case == 4:
            left = {k: Fraction(int(k == (1, 0, 0))) for k in CUBE27}
            right = {k: Fraction(int(k == (1, 1, 0))) for k in CUBE27}
        else:
            left = {k: Fraction((k[0] + 2)**2 - (k[1] + 1)) for k in CUBE27}
            right = {k: Fraction(k[2] - 2 * k[0] + k[1]) for k in CUBE27}

        full = convolution_pair_bilinear(left, right)
        three = convolution_pair_bilinear(left, right, grid=3)
        four = convolution_pair_bilinear(left, right, grid=4)
        five = convolution_pair_bilinear(left, right, grid=5)
        assert all(four[k] == full[k] for k in CUBE27), case
        assert all(five[k] == full[k] for k in WIDE125), case
        profiles.append({
            "case": case,
            "three_retained_matches_exact": all(three[k] == full[k] for k in CUBE27),
            "four_retained_matches_exact": True,
            "five_full_matches_exact": True,
        })

    assert fold(-2, 4) == fold(2, 4) == -2
    assert fold(-2, 5) != fold(2, 5)
    assert fold(2, 3) == -1
    assert profiles[3]["three_retained_matches_exact"] is False
    return profiles


def c3_multiply(x, y):
    """Original Q(omega), omega²=-1-omega, with exact rational components."""
    a, b = x
    c, d = y
    return (a*c - b*d, a*d + b*c - b*d)


def cyclotomic_bilinear_audit():
    left = {
        p: (Fraction(p[0] + 2, 3), Fraction(p[1] - p[2], 7))
        for p in CUBE27
    }
    right = {
        p: (Fraction(p[2] + 1, 5), Fraction(p[0] - p[1], 2))
        for p in CUBE27
    }

    def conv(grid=None):
        output = defaultdict(lambda: (Fraction(0), Fraction(0)))
        for p, q in PAIRS729:
            if grid:
                k = tuple(fold(fold(x, grid) + fold(y, grid), grid)
                          for x, y in zip(p, q))
            else:
                k = integer_sum(p, q)
            a,b = output[k]
            c,d = c3_multiply(left[p], right[q])
            output[k] = (a+c,b+d)
        return output

    exact, four, five = conv(), conv(4), conv(5)
    assert all(four[k] == exact[k] for k in CUBE27)
    assert all(five[k] == exact[k] for k in WIDE125)
    return {
        "coefficients": "original Q(omega) carrier: a+b*omega with omega²=-1-omega",
        "two_independent_complex_like_inputs": True,
        "number_of_input_mode_pairs": len(PAIRS729),
        "four_grid_retained_modes_checked": len(CUBE27),
        "five_grid_full_modes_checked": len(WIDE125),
        "exact_comparison": True,
    }


def audit():
    cases = check_finite_index_pareto()
    cyclo = cyclotomic_bilinear_audit()
    return {
        "scope": "finite quadratic mode-index aggregation, not sampled-field DFT",
        "retained_mode_labels": 27,
        "all_quadratic_output_labels": 125,
        "ordered_pair_interactions": 729,
        "modular_sum_is_computed_from_encoded_inputs": True,
        "three_grid_capacity": 27,
        "four_grid_capacity": 64,
        "five_grid_capacity": 125,
        "four_grid_retained_exact": all(x["four_retained_matches_exact"] for x in cases),
        "four_grid_full_output_injective": False,
        "five_grid_full_output_injective": True,
        "arbitrary_coefficient_theorem": "Agda source-written polymorphic, kernel status not checked",
        "rational_profile_results": cases,
        "cyclotomic_profile": cyclo,
        "full_four_or_five_grid_DFT_proved": False,
        "navier_stokes_regular_or_r2p2_empirical": False,
        "monster_same_object_representation": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
