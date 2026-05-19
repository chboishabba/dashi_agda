"""Edge-only phi-star ratio baseline for the HEPData t43 runner.

This module is intentionally non-promoting.  ``predict_ratio`` is a
calibration/baseline hook for ``scripts/run_t43_projection.py``; it is not an
accepted DASHI empirical adequacy receipt and does not close W3/W4/W5/W8.

The implementation uses only t43 bin edges.  It does not read HEPData ratio
values, uncertainties, covariance entries, or any external calibration file.
"""

from __future__ import annotations

import math
from collections.abc import Mapping
from typing import Any

BASELINE_CLASSIFICATION = "calibration/baseline; non-promoting"
EMPIRICAL_ADEQUACY_RECEIPT_ACCEPTED = False
NON_PROMOTION_BOUNDARY = (
    "no W3 promotion",
    "no W4 promotion",
    "no W5 promotion",
    "no W8 promotion",
    "no empirical adequacy claim",
    "not an accepted DASHI receipt",
)

_MASS_LOW_WINDOW_GEV = (50.0, 76.0)
_MASS_Z_WINDOW_GEV = (76.0, 106.0)
_LAMBDA_QCD_GEV = 0.2
_REFERENCE_RATIO = 0.039


def predict_ratio(bins: list[dict[str, Any]]) -> list[float]:
    """Return one finite baseline ratio for each t43 bin.

    The runner calls this as
    ``DASHI.Physics.Prediction.phi_star_ratio:predict_ratio``.  The returned
    values are deterministic CSS/Sudakov-inspired shape baselines derived from
    ``phiStarLow`` and ``phiStarHigh`` only.
    """

    if not isinstance(bins, list):
        raise TypeError("predict_ratio expects list[dict] t43 bin records")
    return [_predict_bin_ratio(item) for item in bins]


def _predict_bin_ratio(bin_record: Mapping[str, Any]) -> float:
    low = _finite_edge(bin_record, "phiStarLow")
    high = _finite_edge(bin_record, "phiStarHigh")
    if low < 0.0:
        raise ValueError(f"phiStarLow must be non-negative, got {low!r}")
    if high <= low:
        raise ValueError(f"phiStarHigh must be greater than phiStarLow, got {high!r} <= {low!r}")

    numerator = _average_sudakov_weight(low, high, mass_window=_MASS_LOW_WINDOW_GEV)
    denominator = _average_sudakov_weight(low, high, mass_window=_MASS_Z_WINDOW_GEV)
    value = _REFERENCE_RATIO * numerator / denominator

    if not math.isfinite(value):
        raise ArithmeticError("non-finite phi-star baseline ratio")
    return float(value)


def _average_sudakov_weight(low: float, high: float, *, mass_window: tuple[float, float]) -> float:
    """Average a CSS-like no-emission weight across a bin using edge samples."""

    points = _edge_only_quadrature_points(low, high)
    return sum(_sudakov_weight(phi_star, mass_window=mass_window) for phi_star in points) / len(points)


def _edge_only_quadrature_points(low: float, high: float) -> tuple[float, ...]:
    # Interior points are affine combinations of the supplied edges, not data
    # values or fitted knots.  This avoids singular behavior at phi*=0.
    width = high - low
    return (
        low + 0.125 * width,
        low + 0.375 * width,
        low + 0.625 * width,
        low + 0.875 * width,
    )


def _sudakov_weight(phi_star: float, *, mass_window: tuple[float, float]) -> float:
    mass = math.sqrt(mass_window[0] * mass_window[1])
    hard_log = math.log(mass / _LAMBDA_QCD_GEV)
    angular_log = math.log1p(1.0 / max(phi_star, 1.0e-12))

    alpha_eff = _one_loop_alpha_s(mass)
    color_factor = 4.0 / 3.0
    leading = color_factor * alpha_eff / math.pi * angular_log * angular_log
    next_to_leading = 0.08 * alpha_eff * hard_log * angular_log
    recoil_shape = 1.0 / (1.0 + mass * phi_star / 35.0)
    return math.exp(-(leading + next_to_leading)) * recoil_shape


def _one_loop_alpha_s(scale_gev: float) -> float:
    flavors = 5.0
    beta0 = 11.0 - (2.0 / 3.0) * flavors
    denominator = beta0 * math.log((scale_gev / _LAMBDA_QCD_GEV) ** 2)
    return min(0.35, max(0.08, 4.0 * math.pi / denominator))


def _finite_edge(bin_record: Mapping[str, Any], key: str) -> float:
    if key not in bin_record:
        raise KeyError(f"missing required t43 bin edge {key!r}")
    value = float(bin_record[key])
    if not math.isfinite(value):
        raise ValueError(f"{key} must be finite, got {bin_record[key]!r}")
    return value


def metadata() -> dict[str, Any]:
    """Return machine-readable boundary metadata for diagnostics."""

    return {
        "callable": "DASHI.Physics.Prediction.phi_star_ratio:predict_ratio",
        "classification": BASELINE_CLASSIFICATION,
        "acceptedEmpiricalAdequacyReceipt": EMPIRICAL_ADEQUACY_RECEIPT_ACCEPTED,
        "usesOnly": ["phiStarLow", "phiStarHigh"],
        "nonPromotionBoundary": list(NON_PROMOTION_BOUNDARY),
    }


__all__ = [
    "BASELINE_CLASSIFICATION",
    "EMPIRICAL_ADEQUACY_RECEIPT_ACCEPTED",
    "NON_PROMOTION_BOUNDARY",
    "metadata",
    "predict_ratio",
]
