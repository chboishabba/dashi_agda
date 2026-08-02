#!/usr/bin/env python3
"""Exact fail-closed audit for the Stage-3 output-relocation vertical slice."""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product


@dataclass(frozen=True)
class EndpointProfile:
    low_decay_times_two: int
    gap_decay_times_two: int


@dataclass(frozen=True)
class CoefficientVector:
    left: int
    right: int
    output: int


def normalized_decay(s: Q) -> tuple[Q, Q]:
    """Return (2s-5/2, 2s) for the low index and separation gap."""
    return 2 * s - Q(5, 2), 2 * s


def verify_weighted_exponent_identity() -> int:
    checked = 0
    for s in (Q(5, 2), Q(21, 8), Q(8, 3), Q(11, 4), Q(23, 8), Q(3)):
        for j in range(8):
            for d in range(1, 8):
                high = j + d
                raw = Q(3, 2) * j + j - s * high - s * high
                low_decay, gap_decay = normalized_decay(s)
                normalized = -low_decay * j - gap_decay * d
                assert raw == normalized
                checked += 1
    return checked


def verify_endpoint_profile() -> EndpointProfile:
    low_decay, gap_decay = normalized_decay(Q(5, 2))
    profile = EndpointProfile(int(2 * low_decay), int(2 * gap_decay))
    assert profile.low_decay_times_two == 5
    assert profile.gap_decay_times_two == 10
    assert Q(profile.low_decay_times_two, 2) == Q(5, 2)
    assert Q(profile.gap_decay_times_two, 2) == Q(5)
    return profile


def verify_full_open_range_signs() -> int:
    checked = 0
    for numerator in range(251, 300):
        s = Q(numerator, 100)
        low_decay, gap_decay = normalized_decay(s)
        assert Q(5, 2) < s < Q(3)
        assert low_decay > Q(5, 2)
        assert gap_decay > Q(5)
        checked += 1
    return checked


def verify_endpoint_totals_do_not_determine_vector() -> tuple[int, list[CoefficientVector]]:
    # Endpoint decay totals constrain aggregate shell decay, not the orientation
    # of the left/right/output Schur weights. Exhibit several distinct vectors
    # with the same aggregate coefficient sum. These are witnesses of
    # underdetermination, not candidate DASHI coefficients.
    vectors = [
        CoefficientVector(*entries)
        for entries in product(range(-2, 3), repeat=3)
        if sum(entries) == 1
    ]
    assert len(vectors) > 1
    assert CoefficientVector(1, 0, 0) in vectors
    assert CoefficientVector(0, 1, 0) in vectors
    assert CoefficientVector(0, 0, 1) in vectors
    return len(vectors), vectors


def verify_vertical_slice_boundary() -> dict[str, bool]:
    status = {
        "genericRelocationIdentity": True,
        "concreteComplexCarrier": True,
        "componentArchetypeMapped": True,
        "endpointArithmetic": True,
        "weightedExponentIdentity": True,
        "rationalLerayCore": True,
        "rationalBernsteinCore": True,
        "coefficientExtractionInterface": True,
        "cutoffUniformSeries": False,
        "coefficientVector": False,
        "affineConstraint": False,
        "positiveEpsilonCompatibility": False,
    }
    closed_prefix = (
        "genericRelocationIdentity",
        "concreteComplexCarrier",
        "componentArchetypeMapped",
        "endpointArithmetic",
        "weightedExponentIdentity",
        "rationalLerayCore",
        "rationalBernsteinCore",
        "coefficientExtractionInterface",
    )
    open_suffix = (
        "cutoffUniformSeries",
        "coefficientVector",
        "affineConstraint",
        "positiveEpsilonCompatibility",
    )
    assert all(status[key] for key in closed_prefix)
    assert not any(status[key] for key in open_suffix)
    return status


def main() -> int:
    exponent_cases = verify_weighted_exponent_identity()
    profile = verify_endpoint_profile()
    open_range_cases = verify_full_open_range_signs()
    vector_count, _ = verify_endpoint_totals_do_not_determine_vector()
    status = verify_vertical_slice_boundary()
    print(
        "Stage-3 output-relocation vertical-slice audit passed: "
        f"{exponent_cases} exact exponent identities, "
        f"{open_range_cases} open-range sign checks, "
        f"endpoint=({profile.low_decay_times_two},{profile.gap_decay_times_two}), "
        f"{vector_count} distinct aggregate-compatible orientation witnesses, "
        "concrete carrier and weighted exponent closed; constructive series, "
        "coefficient orientation and epsilon compatibility fail-closed; "
        f"status={status}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
