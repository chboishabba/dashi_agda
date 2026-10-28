#!/usr/bin/env python3
"""Exact integer three-mode aliasing and balanced-trit codec diagnostic.

Physics: quadratic Fourier convolutions in pseudo-spectral NS require integer
mode sums before folding into sampled residues. The exact mode support of
[-1,0,+1]^2 is [-2,-1,0,+1,+2]. Folding onto N=3 aliases +2->-1 and
-2->+1. A 5-point grid resolves this *particular* finite product, but is not
a convergence proof, a Navier-Stokes solver, an optical-clock simulation or
a source of experimental findings.

Prior art: Orszag/Patterson; Lambert, Reneuve, Augier, arXiv:2603.08892.
Original DASHI owners: VerifiedFiniteTritCoder, BinaryBalancedTernary-
SubcarrierExact, and NSIntegerFourierLattice (Z^3).
"""
from __future__ import annotations

import argparse
from itertools import product
from collections import defaultdict
import json

MODES = (-1, 0, 1)
CODEC = {-1: (0, 0), 0: (0, 1), 1: (1, 0)}
DECODE = {(0, 0): -1, (0, 1): 0, (1, 0): 1, (1, 1): None}
BINARY_IN_TERNARY = {False: -1, True: 1}


def centered_mod(k: int, n: int) -> int:
    if n % 2 != 1 or n < 3:
        raise ValueError("odd grid n>=3 required")
    return (k + n // 2) % n - n // 2


def exact_quadratic_product(amplitudes: tuple[int, int, int]) -> dict[int, int]:
    """Fourier coefficients of u*u, exact integer convolution."""
    result: dict[int, int] = defaultdict(int)
    for a, av in zip(MODES, amplitudes):
        for b, bv in zip(MODES, amplitudes):
            result[a+b] += av * bv
    return dict(result)


def sampled_quadratic_product(amplitudes: tuple[int, int, int], n: int) -> dict[int, int]:
    """Evaluate a pointwise product on n periodic samples: coefficient folding."""
    result: dict[int, int] = defaultdict(int)
    for k, value in exact_quadratic_product(amplitudes).items():
        result[centered_mod(k, n)] += value
    return dict(result)


def kept_modes(amplitudes: tuple[int, int, int], grid: int):
    full = exact_quadratic_product(amplitudes)
    sampled = sampled_quadratic_product(amplitudes, grid)
    return (
        tuple(full.get(m, 0) for m in MODES),
        tuple(sampled.get(m, 0) for m in MODES),
    )


def audit() -> dict:
    assert all(DECODE[CODEC[m]] == m for m in MODES)
    assert DECODE[(1, 1)] is None
    assert BINARY_IN_TERNARY[False] == -1
    assert BINARY_IN_TERNARY[True] == 1
    assert all(abs(a+b) <= 2 for a,b in product(MODES, repeat=2))
    assert centered_mod(2, 3) == -1
    assert centered_mod(-2, 3) == 1
    assert centered_mod(2, 5) == 2
    assert centered_mod(-2, 5) == -2

    total = 0
    aliased_three = 0
    mismatched_five = 0
    representative = {}
    for v in product(MODES, repeat=3):
        total += 1
        exact, coarse = kept_modes(v, 3)
        exact_five, padded = kept_modes(v, 5)
        assert exact == exact_five
        if exact != coarse:
            aliased_three += 1
        if exact != padded:
            mismatched_five += 1
        if v == (0, 0, 1):
            representative = {
                "input_modes_minus_zero_plus": list(v),
                "exact_retained": list(exact),
                "folded_three_point_retained": list(coarse),
                "padded_five_point_retained": list(padded),
                "untruncated_coeff_plus_two": exact_quadratic_product(v)[2],
            }
    assert total == 27
    assert aliased_three == 24
    assert mismatched_five == 0
    assert representative["exact_retained"] == [0, 0, 0]
    assert representative["folded_three_point_retained"] == [1, 0, 0]
    return {
        "scope": "finite exact quadratic convolution for balanced coefficients",
        "original_N": 3,
        "fully_product_resolving_N": 5,
        "balanced_input_profiles": total,
        "three_point_profiles_with_alias_in_kept_modes": aliased_three,
        "five_point_profiles_with_alias_in_kept_modes": mismatched_five,
        "codec_roundtrip_for_all_three_labels": True,
        "reserved_binary_codeword_rejected": True,
        "binary_subcarrier_uses_only_nonzero_modes": True,
        "example": representative,
        "ns_physical_model_realised": False,
        "ns_clay_or_qg_proved": False,
        "r2p2_optical_clock_measured": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pretty", action="store_true", help="indented audit JSON")
    args = parser.parse_args()
    print(json.dumps(audit(), sort_keys=True, indent=2 if args.pretty else None))


if __name__ == "__main__":
    main()
