"""HEP-R46 mass-kernel calibration diagnostic predictor for t43/t45.

This module is an explicit candidate for the mass-general, unnormalized
differential ratio route for the phistar t43/t45 HEPData tables.

The model follows:

  R(M_num, M_den, φ*) = [BW(M_num) * H(M_num) * S(φ*, M_num)] /
                        [BW(M_den) * H(M_den) * S(φ*, M_den)]

where BW is a Breit-Wigner mass factor, H is a leading-order hard coefficient
approximation, and S is a CSS-like Sudakov ratio proxy.
"""

from __future__ import annotations

import math
from collections.abc import Mapping
from typing import Any

CONSTRUCTION_CLASSIFICATION = "HEP-R46 mass-kernel calibration diagnostic; non-promoting"
MASS_WINDOW_50_76_GEV = (50.0, 76.0)
MASS_WINDOW_76_106_GEV = (76.0, 106.0)
MASS_WINDOW_106_170_GEV = (106.0, 170.0)

ALPHA_EW_AT_MZ = 1.0 / 128.0
M_Z_GEV = 91.1876
Z_WIDTH_GEV = 2.4952
LAMBDA_CONTRACTION = math.log(2.0)
LAMBDA_QCD_GEV = 0.2
BW_STEPS = 2000

NON_PROMOTION_BOUNDARY = (
    "this module is non-promoting: no W3/W4/W5/W8 promotion",
    "does not read observed t43/t45 ratio values",
    "does not read observed uncertainties",
    "does not read covariance inputs",
    "uses first-principles placeholders only",
    "no posterior tuning",
)


def metadata() -> dict[str, Any]:
    """Machine-readable payload for diagnostics and audit logs."""

    return {
        "callable": "DASHI.Physics.Prediction.sigma_dashi_v4:predict_ratio",
        "sigmaCallable": "DASHI.Physics.Prediction.sigma_dashi_v4:sigma_DASHI",
        "classification": CONSTRUCTION_CLASSIFICATION,
        "massWindowsGeV": [
            list(MASS_WINDOW_50_76_GEV),
            list(MASS_WINDOW_76_106_GEV),
            list(MASS_WINDOW_106_170_GEV),
        ],
        "uses": [
            "Breit-Wigner mass integral",
            "running alpha approximation",
            "hard coefficient ratio",
            "log-Sudakov scale ratio",
        ],
        "ignoredInputs": [
            "ratio",
            "uncertainty columns",
            "t43/t45 covariance fields",
        ],
        "nonPromotionBoundary": NON_PROMOTION_BOUNDARY,
    }


def predict_ratio(bins: list[dict[str, Any]]) -> list[float]:
    """Runner-facing 50-76 / 76-106 ratio for t43."""

    return _predict_ratio_for_windows(
        bins,
        MASS_WINDOW_50_76_GEV,
        MASS_WINDOW_76_106_GEV,
    )


def predict_ratio_106_170_over_76_106(bins: list[dict[str, Any]]) -> list[float]:
    """Runner-facing 106-170 / 76-106 ratio for holdout t45."""

    return _predict_ratio_for_windows(
        bins,
        MASS_WINDOW_106_170_GEV,
        MASS_WINDOW_76_106_GEV,
    )


def sigma_DASHI(m_lo: float, m_hi: float, phi_lo: float, phi_hi: float) -> float:
    """Unnormalized carrier proxy for one mass window and one phistar bin."""

    mass_low, mass_high = _finite_mass_window(m_lo, m_hi)
    phi_low = _finite_number(phi_lo, "phi_lo")
    phi_high = _finite_number(phi_hi, "phi_hi")
    if phi_low < 0.0:
        raise ValueError(f"phi_lo must be non-negative, got {phi_lo!r}")
    if phi_high <= phi_low:
        raise ValueError(f"phi_high must exceed phi_lo, got {phi_high!r} <= {phi_low!r}")

    return _sigma_unnormalized(mass_low, mass_high, phi_low, phi_high)


def _predict_ratio_for_windows(
    bins: list[dict[str, Any]],
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> list[float]:
    if not isinstance(bins, list):
        raise TypeError("prediction API expects list[dict] bin records")
    return [
        _predict_bin_ratio(item, numerator_window, denominator_window)
        for item in bins
    ]


def _predict_bin_ratio(
    item: Mapping[str, Any],
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> float:
    phi_low = _finite_edge(item, "phiStarLow")
    phi_high = _finite_edge(item, "phiStarHigh")

    # The observable itself is not integrated in this construction surface.
    # The phistar bin shape enters only through Sudakov ratio.
    phi_mid = 0.5 * (phi_low + phi_high)

    bw_num = _bw_integral(numerator_window[0], numerator_window[1])
    bw_den = _bw_integral(denominator_window[0], denominator_window[1])
    h_num = _hard_coefficient(*numerator_window)
    h_den = _hard_coefficient(*denominator_window)
    s_ratio = _sudakov_ratio(
        phi_mid,
        numerator_window[0],
        numerator_window[1],
        denominator_window[0],
        denominator_window[1],
    )

    base_ratio = (bw_num * h_num) / (bw_den * h_den)
    return float(base_ratio * s_ratio)


def _sigma_unnormalized(m_lo: float, m_hi: float, phi_lo: float, phi_hi: float) -> float:
    phi_mid = 0.5 * (phi_lo + phi_hi)
    m_mid = _mass_midpoint(m_lo, m_hi)
    return _bw_integral(m_lo, m_hi) * _hard_coefficient(m_lo, m_hi) * _shape_proxy(phi_mid, m_mid)


def _shape_proxy(phi_star: float, mass_mid: float) -> float:
    # Smooth bounded shape helper consistent with the Sudakov proxy used in
    # ratio construction.
    return _sudakov_weight(phi_star, mass_mid)


def _sudakov_ratio(
    phi_star: float,
    num_lo: float,
    num_hi: float,
    den_lo: float,
    den_hi: float,
) -> float:
    if phi_star <= 0.0:
        return 1.0

    log_phi = abs(math.log(phi_star))
    d_num = max(0.0, math.log(_mass_midpoint(num_lo, num_hi) / LAMBDA_QCD_GEV) / math.log(3.0))
    d_den = max(0.0, math.log(_mass_midpoint(den_lo, den_hi) / LAMBDA_QCD_GEV) / math.log(3.0))
    s_num = math.exp(-LAMBDA_CONTRACTION * d_num * log_phi)
    s_den = math.exp(-LAMBDA_CONTRACTION * d_den * log_phi)
    return s_num / s_den


def _sudakov_weight(phi_star: float, mass_mid: float) -> float:
    if phi_star <= 0.0:
        phi_star = 1.0e-12
    log_phi = abs(math.log(phi_star))
    depth = max(0.0, math.log(mass_mid / LAMBDA_QCD_GEV) / math.log(3.0))
    return math.exp(-LAMBDA_CONTRACTION * depth * log_phi)


def _hard_coefficient(m_lo: float, m_hi: float) -> float:
    m_mid = _mass_midpoint(m_lo, m_hi)
    alpha_ratio = _running_alpha(m_mid) / ALPHA_EW_AT_MZ
    return (M_Z_GEV / m_mid) ** 2 * (alpha_ratio ** 2)


def _running_alpha(mass_gev: float) -> float:
    # One-loop QED-like running used as narrow placeholder.
    if mass_gev <= 0.0:
        return ALPHA_EW_AT_MZ
    delta_alpha = (ALPHA_EW_AT_MZ / (3.0 * math.pi)) * math.log(mass_gev / M_Z_GEV)
    return ALPHA_EW_AT_MZ / (1.0 - delta_alpha)


def _bw_integral(m_lo: float, m_hi: float, n: int = BW_STEPS) -> float:
    # Drell-Yan-like mass weighting in the chosen window.
    m_low, m_high = _finite_mass_window(m_lo, m_hi)
    width = m_high - m_low
    dm = width / n
    z2 = M_Z_GEV * M_Z_GEV
    wz = (M_Z_GEV * Z_WIDTH_GEV) ** 2
    total = 0.0
    for i in range(n):
        m = m_low + (i + 0.5) * dm
        m2 = m * m
        # The observable is the unnormalised differential ratio Dσ/dφ*,
        # so the leading-beam-energy normalisation used in previous drafts
        # is not included here. The width differential is already handled
        # by ``dm`` and this integral is used only to form a window ratio.
        total += dm / (((m2 - z2) ** 2) + wz)
    return total


def _finite_mass_window(m_lo: float, m_hi: float) -> tuple[float, float]:
    m_low = _finite_number(m_lo, "m_lo")
    m_high = _finite_number(m_hi, "m_hi")
    if m_low < 0.0:
        raise ValueError(f"m_lo must be non-negative, got {m_lo!r}")
    if m_high <= m_low:
        raise ValueError(f"m_hi must be greater than m_lo, got {m_hi!r} <= {m_lo!r}")
    return m_low, m_high


def _finite_edge(bin_record: Mapping[str, Any], key: str) -> float:
    if key not in bin_record:
        raise KeyError(f"missing {key!r} in bin record")
    value = float(bin_record[key])
    if not math.isfinite(value):
        raise ValueError(f"{key} must be finite, got {bin_record[key]!r}")
    return value


def _finite_number(value: float, name: str) -> float:
    value = float(value)
    if not math.isfinite(value):
        raise ValueError(f"{name} must be finite, got {value!r}")
    return value


def _mass_midpoint(m_lo: float, m_hi: float) -> float:
    return 0.5 * (m_lo + m_hi)


__all__ = [
    "CONSTRUCTION_CLASSIFICATION",
    "MASS_WINDOW_50_76_GEV",
    "MASS_WINDOW_76_106_GEV",
    "MASS_WINDOW_106_170_GEV",
    "predict_ratio",
    "predict_ratio_106_170_over_76_106",
    "sigma_DASHI",
    "metadata",
]
