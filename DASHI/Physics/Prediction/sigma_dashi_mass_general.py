"""Mass-window-general DASHI sigma predictor for HEP-R43 diagnostics.

This module is intentionally non-promoting.  It exposes a clean prediction API
for ``scripts/run_t43_projection.py --prediction-api`` without reading observed
t43/t45 ratio values, uncertainties, covariance entries, residuals, or any
external calibration file.

The construction is a deterministic mass-window model:

* a neutral-current mass kernel with Breit-Wigner Z support and photon-like
  continuum support;
* a Drell-Yan-like falling mass flux;
* a small phi-star carrier correction driven only by bin edges and mass ratios.

It is a fresh HEP-R43 diagnostic surface, not a posterior t43 residual patch.
"""

from __future__ import annotations

import math
from collections import namedtuple
from collections.abc import Mapping
from typing import Any

try:  # Prefer a shared structured prediction type if the baseline provides it.
    from DASHI.Physics.Prediction.phi_star_ratio import RatioPrediction as _ImportedRatioPrediction
except Exception:  # pragma: no cover - exercised only when package shape differs.
    _ImportedRatioPrediction = None

_FallbackRatioPrediction = namedtuple(
    "RatioPrediction",
    [
        "value",
        "numerator_sigma",
        "denominator_sigma",
        "numerator_window_gev",
        "denominator_window_gev",
        "phi_star_low",
        "phi_star_high",
        "metadata",
    ],
)

RatioPrediction = _ImportedRatioPrediction or _FallbackRatioPrediction

CONSTRUCTION_CLASSIFICATION = "mass-window-general neutral-current predictor; non-promoting"
ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT = False
POSTERIOR_T43_TUNED = False
PROMOTES_W3 = False

MASS_WINDOW_50_76_GEV = (50.0, 76.0)
MASS_WINDOW_76_106_GEV = (76.0, 106.0)
MASS_WINDOW_106_170_GEV = (106.0, 170.0)

Z_MASS_GEV = 91.1876
Z_WIDTH_GEV = 2.4952
LAMBDA_QCD_GEV = 0.2
MASS_INTEGRATION_STEPS = 192

NON_PROMOTION_BOUNDARY = (
    "fresh HEP-R43 diagnostic predictor only",
    "does not seed from observed t43/t45/t46 Ratio values",
    "does not read uncertainty or covariance entries",
    "does not encode t43 residual-shape corrections",
    "not an accepted empirical adequacy receipt",
    "not enough by itself to promote W3",
    "no W4/W5/W8 promotion",
)


def sigma_DASHI_mass_general(m_lo: float, m_hi: float, phi_lo: float, phi_hi: float) -> float:
    """Return a finite mass-window sigma for one phi-star bin.

    Inputs are only the mass-window edges and phi-star bin edges.  The value is
    an internal diagnostic normalization, not an accepted cross-section claim.
    """

    mass_low, mass_high = _finite_mass_window(m_lo, m_hi)
    phi_low, phi_high = _finite_phi_window(phi_lo, phi_hi)

    phi_average = _average_over_phi(phi_low, phi_high, mass_low, mass_high)
    mass_average = _integrate_mass_kernel(mass_low, mass_high, phi_low, phi_high)
    value = phi_average * mass_average
    if not math.isfinite(value) or value <= 0.0:
        raise ArithmeticError("non-finite or non-positive sigma_DASHI_mass_general")
    return float(value)


def predict_ratio_50_76_over_76_106(bins: list[dict[str, Any]]) -> list[float]:
    """Return 50-76 / 76-106 mass-window ratios for runner compatibility."""

    return _predict_ratio_values(bins, MASS_WINDOW_50_76_GEV, MASS_WINDOW_76_106_GEV)


def predict_ratio_106_170_over_76_106(bins: list[dict[str, Any]]) -> list[float]:
    """Return 106-170 / 76-106 mass-window ratios for holdout diagnostics."""

    return _predict_ratio_values(bins, MASS_WINDOW_106_170_GEV, MASS_WINDOW_76_106_GEV)


def predict_ratio(bins: list[dict[str, Any]]) -> list[float]:
    """Compatibility alias for the t43 50-76 / 76-106 ratio."""

    return predict_ratio_50_76_over_76_106(bins)


def predict_ratio_predictions(
    bins: list[dict[str, Any]],
    numerator_window: tuple[float, float] = MASS_WINDOW_50_76_GEV,
    denominator_window: tuple[float, float] = MASS_WINDOW_76_106_GEV,
) -> list[Any]:
    """Return structured ``RatioPrediction`` diagnostics for each bin.

    The public runner currently validates ``list[float]``, so the runner-facing
    functions return values.  This helper preserves the structured receipt type
    when downstream diagnostics want more context.
    """

    _validate_bins_list(bins, "predict_ratio_predictions")
    return [_ratio_prediction_for_bin(item, numerator_window, denominator_window) for item in bins]


def metadata() -> dict[str, Any]:
    """Return machine-readable governance metadata for diagnostics."""

    return {
        "callable": "DASHI.Physics.Prediction.sigma_dashi_mass_general:predict_ratio",
        "sigmaCallable": "DASHI.Physics.Prediction.sigma_dashi_mass_general:sigma_DASHI_mass_general",
        "classification": CONSTRUCTION_CLASSIFICATION,
        "acceptedEmpiricalAdequacyReceipt": ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT,
        "posteriorT43Tuned": POSTERIOR_T43_TUNED,
        "promotesW3": PROMOTES_W3,
        "massWindowsGeV": [
            list(MASS_WINDOW_50_76_GEV),
            list(MASS_WINDOW_76_106_GEV),
            list(MASS_WINDOW_106_170_GEV),
        ],
        "usesOnly": [
            "massWindowGeV",
            "phiStarLow",
            "phiStarHigh",
            "Breit-Wigner Z mass-window support",
            "neutral-current continuum support",
            "bounded phi-star carrier correction",
            "mass-ratio kinematic correction",
        ],
        "ignoredInputs": [
            "ratio",
            "uncertainties",
            "t44 covariance",
            "t45 observed ratios",
            "t46 covariance",
            "external calibration files",
        ],
        "ratioPredictionType": f"{RatioPrediction.__module__}.{RatioPrediction.__name__}",
        "nonPromotionBoundary": list(NON_PROMOTION_BOUNDARY),
    }


def _predict_ratio_values(
    bins: list[dict[str, Any]],
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> list[float]:
    _validate_bins_list(bins, "predict_ratio")
    return [
        float(_ratio_prediction_for_bin(item, numerator_window, denominator_window).value)
        for item in bins
    ]


def _ratio_prediction_for_bin(
    bin_record: Mapping[str, Any],
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> Any:
    phi_low = _finite_edge(bin_record, "phiStarLow")
    phi_high = _finite_edge(bin_record, "phiStarHigh")
    num_low, num_high = _finite_mass_window(numerator_window[0], numerator_window[1])
    den_low, den_high = _finite_mass_window(denominator_window[0], denominator_window[1])
    numerator = sigma_DASHI_mass_general(num_low, num_high, phi_low, phi_high)
    denominator = sigma_DASHI_mass_general(den_low, den_high, phi_low, phi_high)
    value = numerator / denominator
    if not math.isfinite(value):
        raise ArithmeticError("non-finite mass-general ratio")
    return _make_ratio_prediction(
        value=float(value),
        numerator_sigma=numerator,
        denominator_sigma=denominator,
        numerator_window_gev=(num_low, num_high),
        denominator_window_gev=(den_low, den_high),
        phi_star_low=phi_low,
        phi_star_high=phi_high,
        metadata={
            "acceptedEmpiricalAdequacyReceipt": ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT,
            "posteriorT43Tuned": POSTERIOR_T43_TUNED,
            "promotesW3": PROMOTES_W3,
        },
    )


def _make_ratio_prediction(**payload: Any) -> Any:
    try:
        return RatioPrediction(**payload)
    except TypeError:
        return _FallbackRatioPrediction(**payload)


def _integrate_mass_kernel(mass_low: float, mass_high: float, phi_low: float, phi_high: float) -> float:
    width = mass_high - mass_low
    step = width / MASS_INTEGRATION_STEPS
    total = 0.0
    for index in range(MASS_INTEGRATION_STEPS):
        mass = mass_low + (index + 0.5) * step
        phi_mid = _geometric_midpoint(phi_low, phi_high)
        total += step * _neutral_current_kernel(mass) * _mass_flux(mass) * _mass_ratio_correction(mass, phi_mid)
    return total / width


def _neutral_current_kernel(mass_gev: float) -> float:
    z = _unit_area_breit_wigner(mass_gev)
    continuum = 0.010 * (Z_MASS_GEV / mass_gev) ** 2
    interference = 0.018 * (mass_gev - Z_MASS_GEV) / Z_MASS_GEV
    return max(1.0e-12, z + continuum * (1.0 + interference))


def _unit_area_breit_wigner(mass_gev: float) -> float:
    half_width = 0.5 * Z_WIDTH_GEV
    return (half_width / math.pi) / ((mass_gev - Z_MASS_GEV) ** 2 + half_width * half_width)


def _mass_flux(mass_gev: float) -> float:
    tau_like = mass_gev / Z_MASS_GEV
    return tau_like ** -3.1 * math.exp(-0.22 * max(0.0, tau_like - 1.0))


def _average_over_phi(phi_low: float, phi_high: float, mass_low: float, mass_high: float) -> float:
    values = [
        _phi_carrier_correction(phi_low + fraction * (phi_high - phi_low), mass_low, mass_high)
        for fraction in (0.125, 0.375, 0.625, 0.875)
    ]
    return sum(values) / len(values)


def _phi_carrier_correction(phi_star: float, mass_low: float, mass_high: float) -> float:
    mass_mid = math.sqrt(mass_low * mass_high)
    alpha = _one_loop_alpha_s(mass_mid)
    angular_log = math.log1p(1.0 / max(phi_star, 1.0e-12))
    sudakov = math.exp(-0.18 * alpha * angular_log * angular_log)
    recoil = 1.0 / (1.0 + mass_mid * phi_star / 42.0)
    carrier = 1.0 + 0.035 * math.log(Z_MASS_GEV / mass_mid) * math.tanh(angular_log / 4.0)
    return max(1.0e-9, sudakov * recoil * carrier)


def _mass_ratio_correction(mass_gev: float, phi_star: float) -> float:
    ratio_log = math.log(mass_gev / Z_MASS_GEV)
    soft_angle = math.tanh(math.log1p(1.0 / max(phi_star, 1.0e-12)) / 5.0)
    return max(0.2, 1.0 - 0.06 * ratio_log * soft_angle)


def _one_loop_alpha_s(scale_gev: float) -> float:
    flavors = 5.0
    beta0 = 11.0 - (2.0 / 3.0) * flavors
    denominator = beta0 * math.log((scale_gev / LAMBDA_QCD_GEV) ** 2)
    return min(0.35, max(0.08, 4.0 * math.pi / denominator))


def _geometric_midpoint(low: float, high: float) -> float:
    return math.sqrt(max(low, 1.0e-12) * max(high, 1.0e-12))


def _finite_mass_window(m_lo: float, m_hi: float) -> tuple[float, float]:
    low = float(m_lo)
    high = float(m_hi)
    if not math.isfinite(low) or not math.isfinite(high):
        raise ValueError(f"mass window edges must be finite, got {(m_lo, m_hi)!r}")
    if low <= 0.0 or high <= low:
        raise ValueError(f"mass window must satisfy 0 < low < high, got {(m_lo, m_hi)!r}")
    return low, high


def _finite_phi_window(phi_lo: float, phi_hi: float) -> tuple[float, float]:
    low = float(phi_lo)
    high = float(phi_hi)
    if not math.isfinite(low) or not math.isfinite(high):
        raise ValueError(f"phi-star edges must be finite, got {(phi_lo, phi_hi)!r}")
    if low < 0.0 or high <= low:
        raise ValueError(f"phi-star window must satisfy 0 <= low < high, got {(phi_lo, phi_hi)!r}")
    return low, high


def _finite_edge(bin_record: Mapping[str, Any], key: str) -> float:
    if key not in bin_record:
        raise KeyError(f"missing required phi-star bin edge {key!r}")
    value = float(bin_record[key])
    if not math.isfinite(value):
        raise ValueError(f"{key} must be finite, got {bin_record[key]!r}")
    return value


def _validate_bins_list(bins: list[dict[str, Any]], caller: str) -> None:
    if not isinstance(bins, list):
        raise TypeError(f"{caller} expects list[dict] bin records")


__all__ = [
    "ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT",
    "CONSTRUCTION_CLASSIFICATION",
    "MASS_WINDOW_50_76_GEV",
    "MASS_WINDOW_106_170_GEV",
    "MASS_WINDOW_76_106_GEV",
    "NON_PROMOTION_BOUNDARY",
    "POSTERIOR_T43_TUNED",
    "PROMOTES_W3",
    "RatioPrediction",
    "metadata",
    "predict_ratio",
    "predict_ratio_106_170_over_76_106",
    "predict_ratio_50_76_over_76_106",
    "predict_ratio_predictions",
    "sigma_DASHI_mass_general",
]
