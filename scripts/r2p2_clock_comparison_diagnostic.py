#!/usr/bin/env python3
"""Exact-rational R2P2 software *diagnostic*, not a measured clock or QG test.

Inputs are already-reduced, same-reference fractional-frequency terms.
It does not calculate a physical optical transition, infer a geoid from heights,
extract clock phase from raw RF/optical streams, or validate a data authority.
A source label is never proof of external calibration.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
from typing import Sequence


def comb_frequency(
    mode: int, repetition_hz: Fraction, ceo_hz: Fraction, signed_beat_hz: Fraction
) -> Fraction:
    """Optical reference ν = n f_rep + f_CEO + signed f_beat.

    The instrument must determine the correct tooth and beat sign.
    This function does not infer either one.
    """
    if mode < 0 or repetition_hz <= 0 or not (0 <= ceo_hz < repetition_hz):
        raise ValueError("invalid comb mode, repetition or carrier-envelope offset")
    value = mode * repetition_hz + ceo_hz + signed_beat_hz
    if value <= 0:
        raise ValueError("optical frequency must be positive")
    return value


def determinant3(c: Sequence[Sequence[Fraction]]) -> Fraction:
    return (
        c[0][0] * (c[1][1] * c[2][2] - c[1][2] * c[2][1])
        - c[0][1] * (c[1][0] * c[2][2] - c[1][2] * c[2][0])
        + c[0][2] * (c[1][0] * c[2][1] - c[1][1] * c[2][0])
    )


def validate_covariance(c: Sequence[Sequence[Fraction]]) -> None:
    """Symmetric 3x3 positive-semidefinite check via principal minors."""
    if len(c) != 3 or any(len(row) != 3 for row in c):
        raise ValueError("expected 3x3 covariance")
    for i in range(3):
        if c[i][i] < 0:
            raise ValueError("covariance diagonal is negative")
        for j in range(i + 1, 3):
            if c[i][j] != c[j][i]:
                raise ValueError("covariance must be symmetric")
            if c[i][i] * c[j][j] - c[i][j] * c[j][i] < 0:
                raise ValueError("covariance 2x2 principal minor is negative")
    if determinant3(c) < 0:
        raise ValueError("covariance 3x3 determinant is negative")


@dataclass(frozen=True)
class ReducedClockComparison:
    measured_fractional_ratio: Fraction
    transfer_fractional_correction: Fraction
    predicted_gr_fractional_ratio: Fraction
    covariance: tuple[tuple[Fraction, Fraction, Fraction], ...]
    source_kind: str = "synthetic"

    def analyze(self) -> dict[str, str | bool]:
        if self.source_kind not in ("synthetic", "externally_supplied_unverified"):
            raise ValueError("unrecognized source kind; verified authority not issued here")
        validate_covariance(self.covariance)
        # r = y_measured - y_transfer - y_GR.
        weights = (1, -1, -1)
        residual = (
            self.measured_fractional_ratio
            - self.transfer_fractional_correction
            - self.predicted_gr_fractional_ratio
        )
        variance = sum(
            (
                weights[i] * weights[j] * self.covariance[i][j]
                for i in range(3)
                for j in range(3)
            ),
            Fraction(0),
        )
        if variance < 0:
            raise ValueError("negative residual variance")
        return {
            "residual_fractional": str(residual),
            "residual_variance_fractional_squared": str(variance),
            "source_kind": self.source_kind,
            "external_measurement_authority_verified": False,
            "gravity_deviation_claimed": False,
            "quantum_gravity_claimed": False,
        }


def load_reduced_input(path: Path) -> ReducedClockComparison:
    """Parses unverified input JSON. It cannot promote a source into authority."""
    payload = json.loads(path.read_text(encoding="utf-8"))
    c = tuple(
        tuple(Fraction(str(v)) for v in row)
        for row in payload["covariance"]
    )
    return ReducedClockComparison(
        measured_fractional_ratio=Fraction(str(payload["measured_fractional_ratio"])),
        transfer_fractional_correction=Fraction(str(payload["transfer_fractional_correction"])),
        predicted_gr_fractional_ratio=Fraction(str(payload["predicted_gr_fractional_ratio"])),
        covariance=c,
        source_kind=payload.get("source_kind", "externally_supplied_unverified"),
    )


def synthetic_demonstration() -> ReducedClockComparison:
    """Video slope is a narrated prediction. The matching 'measured' value
    below is fabricated FOR TESTING THE PIPELINE, not based on R2P2 data.
    """
    predicted_video_slope = Fraction(2885, 10**16)
    link_fixture = Fraction(1, 10**17)
    return ReducedClockComparison(
        measured_fractional_ratio=predicted_video_slope + link_fixture,
        transfer_fractional_correction=link_fixture,
        predicted_gr_fractional_ratio=predicted_video_slope,
        covariance=(
            (Fraction(1, 10**36), Fraction(0), Fraction(0)),
            (Fraction(0), Fraction(1, 10**38), Fraction(0)),
            (Fraction(0), Fraction(0), Fraction(1, 10**36)),
        ),
        source_kind="synthetic",
    )


@dataclass(frozen=True)
class TwoBaselineComparison:
    """Conditional affine model: y_i(corrected) = offset + slope * x_i.

    x_i is an externally modelled dimensionless potential difference ΔU_i/c².
    The two rows must represent independent *potential lever arms*, not just
    the two clocks in one mountain-to-ground comparison. Equal/stable nuisance
    bias, calibrated x, covariance and source authority are NOT inferred.
    """

    x1: Fraction
    x2: Fraction
    measured1: Fraction
    measured2: Fraction
    transfer1: Fraction
    transfer2: Fraction
    corrected_covariance: tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]
    source_kind: str = "synthetic"

    def analyze(self) -> dict[str, str | bool]:
        if self.source_kind not in ("synthetic", "externally_supplied_unverified"):
            raise ValueError("no evidence authority can be constructed by this parser")
        dx = self.x2 - self.x1
        if dx == 0:
            raise ValueError("two independent potential lever arms are necessary")
        c = self.corrected_covariance
        if len(c) != 2 or any(len(row) != 2 for row in c):
            raise ValueError("expected 2x2 covariance for corrected clock ratios")
        if c[0][1] != c[1][0] or c[0][0] < 0 or c[1][1] < 0:
            raise ValueError("covariance must be symmetric with nonnegative diagonal")
        if c[0][0] * c[1][1] < c[0][1] * c[0][1]:
            raise ValueError("covariance is not positive semidefinite")
        y1 = self.measured1 - self.transfer1
        y2 = self.measured2 - self.transfer2
        slope = (y2 - y1) / dx
        intercept = y1 - slope * self.x1
        var_slope = (c[0][0] + c[1][1] - 2 * c[0][1]) / (dx * dx)
        if var_slope < 0:
            raise ValueError("negative slope variance")
        return {
            "conditional_slope": str(slope),
            "conditional_bias": str(intercept),
            "slope_variance_if_potentials_exact": str(var_slope),
            "source_kind": self.source_kind,
            "same_bias_across_baselines_proven": False,
            "geopotential_calibrated_here": False,
            "external_measurement_authority_verified": False,
            "quantum_gravity_claimed": False,
        }


def load_two_baseline_input(path: Path) -> TwoBaselineComparison:
    payload = json.loads(path.read_text(encoding="utf-8"))
    return TwoBaselineComparison(
        x1=Fraction(str(payload["potential_ratio_1"])),
        x2=Fraction(str(payload["potential_ratio_2"])),
        measured1=Fraction(str(payload["measured_fractional_ratio_1"])),
        measured2=Fraction(str(payload["measured_fractional_ratio_2"])),
        transfer1=Fraction(str(payload["transfer_correction_1"])),
        transfer2=Fraction(str(payload["transfer_correction_2"])),
        corrected_covariance=tuple(
            tuple(Fraction(str(v)) for v in row)
            for row in payload["corrected_covariance"]
        ),
        source_kind=payload.get("source_kind", "externally_supplied_unverified"),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="Reduced ratio/covariance JSON, never auto-verified")
    parser.add_argument("--two-baseline-input", type=Path,
                        help="Two distinct potential lever arms and corrected 2x2 covariance JSON")
    args = parser.parse_args()
    if args.input and args.two_baseline_input:
        parser.error("choose one input mode only")
    comparison = (
        load_two_baseline_input(args.two_baseline_input)
        if args.two_baseline_input else
        load_reduced_input(args.input) if args.input else
        synthetic_demonstration()
    )
    print(json.dumps(comparison.analyze(), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
