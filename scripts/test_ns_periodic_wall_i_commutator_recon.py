#!/usr/bin/env python3
"""Fast regressions for the exact far-low commutator reconnaissance."""
from __future__ import annotations

from fractions import Fraction

from ns_periodic_wall_i_commutator_recon import (
    commutator_recon_report,
    far_low_bilinear_symbol,
    far_low_kernel_triple,
    tensor_flatten,
    tensor_l1,
)
from ns_periodic_wall_i_lab import hat_multiplier, rho


def main() -> int:
    zero_symbol = far_low_bilinear_symbol(
        (0, 0, 0), (1, 0, 0), (1, 0, 0), 0, 1
    )
    assert tensor_l1(zero_symbol) == 0

    low = (1, 0, 0)
    high = (1, 1, 0)
    output = (2, 1, 0)
    triple = far_low_kernel_triple(low, high, output, 1, 1)
    expected_difference = (
        hat_multiplier(1, rho(output)) - hat_multiplier(1, rho(high))
    )
    assert triple.difference_factor == expected_difference
    assert tuple(abs(x) for x in tensor_flatten(triple.difference)) == tensor_flatten(
        triple.absolute_difference
    )

    report = commutator_recon_report(
        cutoff=2,
        output_shell=1,
        separation=1,
        overlap=1,
        weight_exponent=1,
        target_separation=8,
        max_entries=100_000,
    )
    assert report.exact_complete
    assert report.max_cutoff_level == 1
    assert not report.target_separation_geometrically_accessible
    assert Fraction(report.absolute_difference_schur.product) >= 0
    print("[ok] far-low commutator reconnaissance regressions passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
