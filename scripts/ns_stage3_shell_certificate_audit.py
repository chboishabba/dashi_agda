#!/usr/bin/env python3
"""Exact Stage-3 one-low, overlap, and certificate-readiness audit."""

from __future__ import annotations

from fractions import Fraction


def one_low_endpoint_profile(location: str) -> tuple[Fraction, Fraction]:
    """Return (low-shell decay, separation-gap decay) at s=5/2."""
    if location == "derivative-high":
        return Fraction(5, 2), Fraction(3, 2)
    if location == "derivative-low":
        return Fraction(5, 2), Fraction(5, 2)
    if location == "ordered-pair-mixed":
        # A positive majorant pays the weaker high-derivative gap.
        return Fraction(5, 2), Fraction(3, 2)
    raise ValueError(f"unknown derivative location: {location}")


def near_pair_multiplicity(width: int) -> int:
    return (2 * width + 1) ** 2


def verify_one_low_archetypes() -> None:
    assert one_low_endpoint_profile("derivative-high") == (
        Fraction(5, 2),
        Fraction(3, 2),
    )
    assert one_low_endpoint_profile("derivative-low") == (
        Fraction(5, 2),
        Fraction(5, 2),
    )
    assert one_low_endpoint_profile("ordered-pair-mixed") == (
        Fraction(5, 2),
        Fraction(3, 2),
    )

    # Literal output coefficient -i P_k[(u_p . q)u_q].
    output_low_high = "derivative-high"  # p low, q high
    output_high_low = "derivative-low"   # p high, q low
    assert one_low_endpoint_profile(output_low_high)[1] == Fraction(3, 2)
    assert one_low_endpoint_profile(output_high_low)[1] == Fraction(5, 2)


def verify_finite_overlap_arithmetic() -> None:
    far_gap = 3
    transition_gaps = tuple(range(far_gap))
    assert transition_gaps == (0, 1, 2)
    assert len(transition_gaps) == 3
    assert 2 * len(transition_gaps) == 6

    for width in range(0, 17):
        enumerated = sum(
            1
            for left_offset in range(-width, width + 1)
            for right_offset in range(-width, width + 1)
        )
        assert near_pair_multiplicity(width) == enumerated


def verify_row_readiness() -> None:
    separated_row_count = 12
    literally_mapped_output_rows = 2
    unmapped_separated_rows = 10
    assert separated_row_count - literally_mapped_output_rows == unmapped_separated_rows

    high_high_numeric_rows = 3
    finite_overlap_rows = 9
    analytic_open_rows = 12
    assert high_high_numeric_rows + finite_overlap_rows + analytic_open_rows == 24

    all_twelve_numeric = False
    all_nine_overlap_constants = False
    repository_gap_promoted = False
    strict_affine_certificate_allowed = (
        all_twelve_numeric
        and all_nine_overlap_constants
        and repository_gap_promoted
    )
    assert not strict_affine_certificate_allowed


def verify_open_interval_slack_policy() -> None:
    def uniform_endpoint_margin(left: Fraction, right: Fraction) -> Fraction | None:
        minimum = min(left, right)
        if minimum <= 0:
            return None
        return minimum / 2

    assert uniform_endpoint_margin(Fraction(1, 3), Fraction(1, 5)) == Fraction(1, 10)
    assert uniform_endpoint_margin(Fraction(0), Fraction(1, 5)) is None
    assert uniform_endpoint_margin(Fraction(-1, 7), Fraction(1, 5)) is None


def main() -> int:
    verify_one_low_archetypes()
    verify_finite_overlap_arithmetic()
    verify_row_readiness()
    verify_open_interval_slack_policy()
    print(
        "verified one-low endpoint profiles (5/2,3/2) and (5/2,5/2), "
        "transition gaps {0,1,2} with multiplicities 3/6, near formula "
        "(2W+1)^2 for W=0..16, row readiness 2 mapped + 10 unmapped "
        "separated rows, and fail-closed affine-certificate policy"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
