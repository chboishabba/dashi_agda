#!/usr/bin/env python3
"""Exact endpoint, gap, and fail-closed affine-readiness audit for Stage 3."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction


class Leg(Enum):
    OUTPUT = "output"
    FIRST = "first-adjoint"
    SECOND = "second-adjoint"


class ShellClass(Enum):
    LOW_HIGH = "low-high"
    HIGH_LOW = "high-low"
    HIGH_HIGH_TO_LOW = "high-high-to-low"
    NEAR = "near"
    FAR_LOW = "far-low"
    FAR_HIGH = "far-high"
    TRANSITION = "transition"
    RESIDUAL = "residual"


class RowStatus(Enum):
    NUMERIC_EXPONENT_CLOSED = "numeric-exponent-closed"
    FINITE_OVERLAP_ONLY = "finite-overlap-only"
    ANALYTIC_OPEN = "analytic-open"


@dataclass(frozen=True)
class EndpointDecay:
    low_decay_times_two: int
    gap_decay_times_two: int


ENDPOINT = {
    Leg.OUTPUT: EndpointDecay(5, 10),
    Leg.FIRST: EndpointDecay(5, 8),
    Leg.SECOND: EndpointDecay(5, 10),
}


LEDGER_STATUS = {
    (leg, shell_class): (
        RowStatus.NUMERIC_EXPONENT_CLOSED
        if shell_class is ShellClass.HIGH_HIGH_TO_LOW
        else RowStatus.FINITE_OVERLAP_ONLY
        if shell_class in {ShellClass.NEAR, ShellClass.TRANSITION, ShellClass.RESIDUAL}
        else RowStatus.ANALYTIC_OPEN
    )
    for leg in Leg
    for shell_class in ShellClass
}


def endpoint_decay_from_formula(leg: Leg, s: Fraction) -> EndpointDecay:
    # Powers are rewritten with J=j+d and scaled by two.
    # Output/second: 2^(5j/2 - 2sJ).
    # First:         2^(3j/2 + J - 2sJ).
    low_decay = 4 * s - 5
    if leg is Leg.FIRST:
        gap_decay = 4 * s - 2
    else:
        gap_decay = 4 * s
    assert low_decay.denominator == 1
    assert gap_decay.denominator == 1
    return EndpointDecay(int(low_decay), int(gap_decay))


def verify_tail_endpoint() -> None:
    lower = Fraction(5, 2)
    for leg in Leg:
        assert endpoint_decay_from_formula(leg, lower) == ENDPOINT[leg]

    # Both decay magnitudes increase with s, so the limiting lower endpoint is
    # the worst case on 5/2 < s < 3.
    upper = Fraction(3)
    for leg in Leg:
        upper_decay = endpoint_decay_from_formula(leg, upper)
        assert upper_decay.low_decay_times_two > ENDPOINT[leg].low_decay_times_two
        assert upper_decay.gap_decay_times_two > ENDPOINT[leg].gap_decay_times_two


def ratio_bound(gap: int) -> Fraction:
    # low <= 2^(j+1), high >= 2^J, J-j >= gap.
    return Fraction(2, 2**gap)


def verify_gap_three() -> None:
    admissible = [gap for gap in range(0, 10) if ratio_bound(gap) <= Fraction(1, 4)]
    assert admissible[0] == 3
    assert ratio_bound(3) == Fraction(1, 4)

    lower = Fraction(1) - ratio_bound(3)
    upper = Fraction(1) + ratio_bound(3)
    assert lower == Fraction(3, 4)
    assert upper == Fraction(5, 4)

    # If high is in shell J, output lies strictly between shell boundaries
    # J-1 and J+2, hence has shell offset at most one.
    assert lower > Fraction(1, 2)
    assert upper * 2 < 4


def verify_fail_closed_affine_readiness() -> tuple[int, int, int]:
    numeric = sum(status is RowStatus.NUMERIC_EXPONENT_CLOSED for status in LEDGER_STATUS.values())
    overlap = sum(status is RowStatus.FINITE_OVERLAP_ONLY for status in LEDGER_STATUS.values())
    open_rows = sum(status is RowStatus.ANALYTIC_OPEN for status in LEDGER_STATUS.values())
    assert (numeric, overlap, open_rows) == (3, 9, 12)

    all_numeric = all(status is RowStatus.NUMERIC_EXPONENT_CLOSED for status in LEDGER_STATUS.values())
    certificate_emitted = False
    assert not all_numeric
    assert not certificate_emitted
    return numeric, overlap, open_rows


def main() -> int:
    verify_tail_endpoint()
    verify_gap_three()
    numeric, overlap, open_rows = verify_fail_closed_affine_readiness()
    print(
        "verified lower-endpoint tail margins "
        "(output 5/2,5; first 5/2,4; second 5/2,5), "
        "minimal geometric far gap G=3 with 3/4--5/4 comparability, and "
        f"fail-closed affine readiness: {numeric} numeric rows, "
        f"{overlap} finite-overlap rows, {open_rows} analytic rows open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
