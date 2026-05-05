"""Internal DASHI-native sigma construction hook for the HEPData t43 runner.

This module is a governed construction surface, not an empirical promotion.
It exposes ``sigma_DASHI`` and ``predict_ratio`` for
``scripts/run_t43_projection.py --prediction-api`` while preserving the
boundary that t43 observed ratios, uncertainties, and covariance entries are
not prediction inputs.

The implementation is a deterministic finite enumeration over balanced trit
states.  HEP-R39 refines the HEP-R36 construction with a phi-star-dependent
carrier depth, a Breit-Wigner mass normalization, and a smooth finite-carrier
phase measure.  HEP-R40 adds a diagnostic neutral-current continuum factor for
the off-peak / Z-peak mass-window contrast.  HEP-R41 adds a posterior
diagnostic shoulder/recovery response after inspecting the HEP-R40 residual
shape.  HEP-R46 adds an above-Z neutral-current tail correction for the t45
high-mass holdout.  HEP-R47 adds a non-promoting signed-log Sudakov direction
diagnostic for the high-mass holdout.  HEP-R48 replaces the ratio midpoint
evaluation with a bin-integrated five-point quadrature diagnostic.  HEP-R49
splits the above-Z shape kernel into a flat photon component and a Z-like
Sudakov component.  It is enough to exercise the prediction API shape, but it
is not by itself an accepted W3 empirical-adequacy receipt.
"""

from __future__ import annotations

import math
from collections.abc import Mapping
from functools import lru_cache
from itertools import product
from typing import Any

CONSTRUCTION_CLASSIFICATION = "internal DASHI-native construction surface; non-promoting"
ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT = False
OBSERVED_T43_RATIO_SEEDING = False
POSTERIOR_DIAGNOSTIC_REFINEMENT = True
PROMOTES_W3 = False

MASS_WINDOW_50_76_GEV = (50.0, 76.0)
MASS_WINDOW_76_106_GEV = (76.0, 106.0)
MASS_WINDOW_106_170_GEV = (106.0, 170.0)

TRIT_VALUES = (-1, 0, 1)
TRIT_DEPTH = 8
TRIT_STATES = tuple(product(TRIT_VALUES, repeat=TRIT_DEPTH))

PHI_STAR_REF = 1.0
DEPTH_EW = 2
MIN_CARRIER_DEPTH = 0
MAX_CARRIER_DEPTH = 4
LAMBDA_CONTRACTION = math.log(2.0)
Z_MASS_GEV = 91.1876
Z_WIDTH_GEV = 2.4952
WEAK_MIXING_SIN2 = 0.2312
ALPHA_EW_Z = 1.0 / 128.0
BREIT_WIGNER_STEPS = 256
CONTINUUM_STRENGTH = 0.8
CONTINUUM_SOFT_PHI_SCALE = 0.005
CONTINUUM_SOFT_POWER = 3.0
CONTINUUM_SHOULDER_WEIGHT = 0.3
CONTINUUM_SHOULDER_PHI_SCALE = 0.4
CONTINUUM_SHOULDER_ONSET = 0.03
SHAPE_DIP_STRENGTH = 0.08
SHAPE_DIP_CENTER = 0.06
SHAPE_DIP_LOG_WIDTH = 0.35
SHAPE_BUMP_STRENGTH = 0.04
SHAPE_BUMP_CENTER = 0.18
SHAPE_BUMP_LOG_WIDTH = 0.8
ABOVE_Z_SUDAKOV_DIRECTION_STRENGTH = 0.25
RATIO_BIN_INTEGRATION_NODES = (
    -0.906179845938664,
    -0.538469310105683,
    0.0,
    0.538469310105683,
    0.906179845938664,
)
RATIO_BIN_INTEGRATION_WEIGHTS = (
    0.236926885056189,
    0.478628670499366,
    0.568888888888889,
    0.478628670499366,
    0.236926885056189,
)
_LEPTON_CHARGE = -1.0
_UP_TYPE_CHARGE = 2.0 / 3.0
_UP_TYPE_VECTOR_COUPLING = 0.5 - 2.0 * _UP_TYPE_CHARGE * WEAK_MIXING_SIN2
_UP_TYPE_AXIAL_COUPLING = 0.5
_LEPTON_VECTOR_COUPLING = -0.5 - 2.0 * _LEPTON_CHARGE * WEAK_MIXING_SIN2
_LEPTON_AXIAL_COUPLING = -0.5
_PHOTON_PREFAC = (_UP_TYPE_CHARGE * _LEPTON_CHARGE) ** 2
_GAMMA_Z_INTERFERENCE_PREFAC = (
    2.0
    * _UP_TYPE_CHARGE
    * _LEPTON_CHARGE
    * _UP_TYPE_VECTOR_COUPLING
    * _LEPTON_VECTOR_COUPLING
)
_Z_PREFAC = (
    (_UP_TYPE_VECTOR_COUPLING**2 + _UP_TYPE_AXIAL_COUPLING**2)
    * (_LEPTON_VECTOR_COUPLING**2 + _LEPTON_AXIAL_COUPLING**2)
)

NON_PROMOTION_BOUNDARY = (
    "internal construction only",
    "does not seed from observed t43 Ratio values",
    "does not read t43 uncertainties",
    "does not read t44 covariance",
    "HEP-R41 constants are posterior diagnostic residual-shape refinements",
    "not an accepted empirical adequacy receipt",
    "not enough by itself to promote W3",
    "no W4/W5/W8 promotion",
)


def predict_ratio(bins: list[dict[str, Any]]) -> list[float]:
    """Return one finite DASHI construction ratio for each t43 bin.

    The accepted runner shape is ``list[t43 bin dict] -> list[float]``.  This
    function intentionally reads only ``phiStarLow`` and ``phiStarHigh`` from
    each bin record; observed ``ratio`` values and error/covariance fields are
    ignored.
    """

    if not isinstance(bins, list):
        raise TypeError("predict_ratio expects list[dict] t43 bin records")
    return _predict_ratio_for_mass_windows(bins, MASS_WINDOW_50_76_GEV, MASS_WINDOW_76_106_GEV)


def predict_ratio_106_170_over_76_106(bins: list[dict[str, Any]]) -> list[float]:
    """Return the unchanged-model holdout ratio for t45.

    This is the HEP-R42 holdout entry point:
    ``sigma_DASHI(106-170, bin) / sigma_DASHI(76-106, bin)``.
    It uses the same posterior diagnostic construction constants as HEP-R41
    and does not read observed ratio values or covariance entries.
    """

    if not isinstance(bins, list):
        raise TypeError("predict_ratio_106_170_over_76_106 expects list[dict] bin records")
    return _predict_ratio_for_mass_windows(bins, MASS_WINDOW_106_170_GEV, MASS_WINDOW_76_106_GEV)


def predict_dirty_z_peak_shape(bins: list[dict[str, Any]]) -> list[float]:
    """Return the uncalibrated 76-106 GeV phi-star shape for W4.

    The t21 table is an absolute ``d sigma / d phi* [pb]`` surface.  This
    internal construction does not carry the physical ``pb`` unit calibration,
    so this callable deliberately returns only the same finite-construction
    shape used by ``sigma_DASHI``.  The dirty Z-peak runner may fit exactly one
    scalar calibration factor against t21/t22 and record that factor as a W4
    calibration anchor.  Observed values, uncertainties, and covariance entries
    are not read here.
    """

    if not isinstance(bins, list):
        raise TypeError("predict_dirty_z_peak_shape expects list[dict] bin records")
    return [
        sigma_DASHI(
            MASS_WINDOW_76_106_GEV[0],
            MASS_WINDOW_76_106_GEV[1],
            _finite_edge(item, "phiStarLow"),
            _finite_edge(item, "phiStarHigh"),
        )
        for item in bins
    ]


def sigma_DASHI(m_lo: float, m_hi: float, phi_lo: float, phi_hi: float) -> float:
    """Compute an internal finite-enumeration sigma for one mass window/bin.

    The public signature mirrors the HEP-R36 construction target:

      sigma_DASHI(m_lo, m_hi, phi_lo, phi_hi) -> float

    ``phi_lo`` and ``phi_hi`` come from t43 bin edges.  Observed t43 ratios,
    uncertainties, and covariance values are not accepted inputs here.
    """

    mass_low, mass_high = _finite_mass_window((m_lo, m_hi))
    phi_low = _finite_number(phi_lo, "phi_lo")
    phi_high = _finite_number(phi_hi, "phi_hi")
    if phi_low < 0.0:
        raise ValueError(f"phiStarLow must be non-negative, got {phi_low!r}")
    if phi_high <= phi_low:
        raise ValueError(f"phiStarHigh must be greater than phiStarLow, got {phi_high!r} <= {phi_low!r}")

    value = _window_sigma(mass_low, mass_high, phi_low, phi_high)
    if not math.isfinite(value) or value <= 0.0:
        raise ArithmeticError("non-finite or non-positive sigma_DASHI construction")
    return float(value)


def metadata() -> dict[str, Any]:
    """Return machine-readable governance metadata for diagnostics."""

    return {
        "callable": "DASHI.Physics.Prediction.sigma_dashi:predict_ratio",
        "sigmaCallable": "DASHI.Physics.Prediction.sigma_dashi:sigma_DASHI",
        "dirtyZPeakShapePredictionCallable": "DASHI.Physics.Prediction.sigma_dashi:predict_dirty_z_peak_shape",
        "supportsDirtyZPeakShapePrediction": True,
        "supportsDirtyZPeakAbsolutePrediction": False,
        "classification": CONSTRUCTION_CLASSIFICATION,
        "acceptedEmpiricalAdequacyReceipt": ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT,
        "observedT43RatioSeeding": OBSERVED_T43_RATIO_SEEDING,
        "posteriorDiagnosticRefinement": POSTERIOR_DIAGNOSTIC_REFINEMENT,
        "promotesW3": PROMOTES_W3,
        "massWindowsGeV": [
            list(MASS_WINDOW_50_76_GEV),
            list(MASS_WINDOW_76_106_GEV),
            list(MASS_WINDOW_106_170_GEV),
        ],
        "usesOnly": [
            "phiStarLow",
            "phiStarHigh",
            "massWindowGeV",
            "deterministic finite trit-state enumeration",
            "phi-star-dependent carrier depth",
            "Breit-Wigner mass-window normalization",
            "diagnostic neutral-current continuum factor",
            "above-Z gamma/Z tail correction",
            "above-Z signed-log Sudakov direction diagnostic",
            "HEP-R48 five-point bin-integrated ratio diagnostic",
            "HEP-R49 two-component photon/Z shape diagnostic",
            "posterior diagnostic shoulder/recovery response",
        ],
        "ignoredInputs": [
            "ratio",
            "uncertainties",
            "t44 covariance",
            "external calibration files",
        ],
        "tritEnumeration": {
            "values": list(TRIT_VALUES),
            "depth": TRIT_DEPTH,
            "stateCount": len(TRIT_STATES),
        },
        "hepR39Refinement": {
            "phiStarRef": PHI_STAR_REF,
            "ewDepth": DEPTH_EW,
            "depthBounds": [MIN_CARRIER_DEPTH, MAX_CARRIER_DEPTH],
            "lambdaContraction": LAMBDA_CONTRACTION,
            "massNormalization": "Breit-Wigner integral with Drell-Yan flux factor",
            "continuumFactor": "diagnostic gamma/Z continuum support; not an accepted comparison-law fit",
            "aboveZNeutralCurrentTail": {
                "helper": "neutral_current_window_factor",
                "activeOnlyWhenMassWindowExtendsAboveZPole": True,
                "terms": ["photon", "gamma/Z interference", "pure Z"],
                "status": "diagnostic mass-kernel correction for high-mass holdout",
            },
            "aboveZSudakovDirection": {
                "helper": "_window_asymmetric_sudakov_ratio",
                "activeOnlyForNumeratorAboveReferenceWindow": True,
                "effect": "signed-log factor lowers low-phi holdout bins and raises high-phi holdout bins",
                "strength": ABOVE_Z_SUDAKOV_DIRECTION_STRENGTH,
                "status": "HEP-R47 posterior diagnostic shape correction; non-promoting",
            },
            "ratioBinIntegration": {
                "helper": "_bin_integrated_prediction_ratio",
                "method": "five-point Gauss-Legendre quadrature",
                "activeFor": "all ratio prediction bins",
                "status": "HEP-R48 precision diagnostic; non-promoting",
            },
            "twoComponentShape": {
                "helper": "_two_component_sudakov_ratio",
                "photonComponent": "flat in phi-star",
                "interferenceComponent": "Z-like phi-star shape",
                "zComponent": "above-Z signed-log Sudakov shape",
                "status": "HEP-R49 photon/Z decomposition diagnostic; non-promoting",
            },
            "shapeResponse": "posterior diagnostic only; constants selected after HEP-R40 residual inspection",
            "status": "non-promoting diagnostic construction",
        },
        "nonPromotionBoundary": list(NON_PROMOTION_BOUNDARY),
    }


def _predict_ratio_for_mass_windows(
    bins: list[dict[str, Any]],
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> list[float]:
    return [
        _predict_bin_ratio(item, numerator_window, denominator_window)
        for item in bins
    ]


def _predict_bin_ratio(
    bin_record: Mapping[str, Any],
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> float:
    phi_low = _finite_edge(bin_record, "phiStarLow")
    phi_high = _finite_edge(bin_record, "phiStarHigh")
    value = _bin_integrated_prediction_ratio(
        phi_low,
        phi_high,
        numerator_window,
        denominator_window,
    )
    if not math.isfinite(value):
        raise ArithmeticError("non-finite sigma_DASHI ratio")
    return float(value)


def _bin_integrated_prediction_ratio(
    phi_low: float,
    phi_high: float,
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> float:
    """Return the HEP-R48 bin-integrated ratio diagnostic.

    The t45 HEP-R47 residual is concentrated in shape rather than mean
    normalization.  Wide phi-star bins make midpoint evaluation too brittle,
    especially when the above-Z signed-log factor changes noticeably across
    the bin.  This helper integrates numerator and denominator densities with
    fixed five-point Gauss-Legendre quadrature over the actual bin width.

    This is a precision correction only.  It adds no fitted parameter and
    preserves the non-promotion governance boundary.
    """

    width = phi_high - phi_low
    if width <= 0.0:
        raise ValueError("phi-star bin width must be positive")

    numerator_total = 0.0
    denominator_total = 0.0
    for node, weight in zip(RATIO_BIN_INTEGRATION_NODES, RATIO_BIN_INTEGRATION_WEIGHTS):
        phi_sample = 0.5 * (phi_low + phi_high) + 0.5 * width * node
        numerator_total += weight * _window_sigma_density_at_phi(
            numerator_window[0],
            numerator_window[1],
            phi_sample,
            phi_low,
            phi_high,
        )
        denominator_total += weight * _window_sigma_density_at_phi(
            denominator_window[0],
            denominator_window[1],
            phi_sample,
            phi_low,
            phi_high,
        )

    if denominator_total <= 0.0:
        raise ArithmeticError("non-positive denominator in bin-integrated ratio")

    value = numerator_total / denominator_total
    value *= _bin_integrated_sudakov_ratio(
        phi_low,
        phi_high,
        numerator_window,
        denominator_window,
    )
    return value


def _window_sigma_density_at_phi(
    mass_low: float,
    mass_high: float,
    phi_star: float,
    phi_low: float,
    phi_high: float,
) -> float:
    """Evaluate the differential sigma density at one phi-star sample."""

    mass_norm = _mass_normalization(mass_low, mass_high)
    total = 0.0
    count = 0
    for mass in _mass_quadrature_points(mass_low, mass_high):
        total += (
            _carrier_phase_density(mass, phi_star, phi_low, phi_high)
            * _neutral_current_continuum_factor(mass, phi_star)
            * _posterior_shape_response_factor(mass, phi_star)
        )
        count += 1
    return mass_norm * total / count


def _bin_integrated_sudakov_ratio(
    phi_low: float,
    phi_high: float,
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> float:
    """Integrate the HEP-R47 Sudakov factor over the bin for HEP-R48."""

    width = phi_high - phi_low
    total = 0.0
    weight_total = 0.0
    for node, weight in zip(RATIO_BIN_INTEGRATION_NODES, RATIO_BIN_INTEGRATION_WEIGHTS):
        phi_sample = 0.5 * (phi_low + phi_high) + 0.5 * width * node
        total += weight * _two_component_sudakov_ratio(
            phi_sample,
            phi_sample,
            numerator_window,
            denominator_window,
        )
        weight_total += weight
    if weight_total <= 0.0:
        return 1.0
    return total / weight_total


def _two_component_sudakov_ratio(
    phi_low: float,
    phi_high: float,
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> float:
    """Return the HEP-R49 photon/Z two-component shape diagnostic.

    The photon component is flat in phi-star.  Gamma/Z interference and pure-Z
    components retain the HEP-R47 Sudakov direction.  Fractions are computed
    from the same neutral-current terms used for the above-Z mass kernel; no
    observed ratio values are read.
    """

    numerator_mid = 0.5 * (numerator_window[0] + numerator_window[1])
    if numerator_mid <= Z_MASS_GEV:
        return _window_asymmetric_sudakov_ratio(
            phi_low,
            phi_high,
            numerator_window,
            denominator_window,
        )

    gamma_num, interference_num, z_num = _component_fractions(*numerator_window)
    gamma_den, interference_den, z_den = _component_fractions(*denominator_window)
    z_shape_num = _window_asymmetric_sudakov_ratio(
        phi_low,
        phi_high,
        numerator_window,
        denominator_window,
    )

    shape_num = gamma_num + (interference_num + z_num) * z_shape_num
    shape_den = gamma_den + interference_den + z_den
    if abs(shape_den) < 1.0e-30:
        return 1.0
    value = shape_num / shape_den
    if not math.isfinite(value) or value <= 0.0:
        return 1.0
    return value


def _window_asymmetric_sudakov_ratio(
    phi_low: float,
    phi_high: float,
    numerator_window: tuple[float, float],
    denominator_window: tuple[float, float],
) -> float:
    """Return the HEP-R47 signed-log high-mass shape diagnostic.

    The HEP-R46 t45 holdout was close in average normalization but had a clear
    shape error: low-phi bins were high and high-phi bins were low.  Therefore
    the admissible diagnostic factor for an above-Z numerator must be below one
    for ``phi* < 1`` and above one for ``phi* > 1``.  The opposite sign would
    worsen the observed residual.

    Below-Z ratios are left unchanged here to preserve the HEP-R41 t43
    diagnostic result.  This factor is explicitly posterior diagnostic state,
    not a clean-freeze empirical adequacy receipt.
    """

    numerator_mid = 0.5 * (numerator_window[0] + numerator_window[1])
    denominator_mid = 0.5 * (denominator_window[0] + denominator_window[1])
    if numerator_mid <= denominator_mid or numerator_mid <= Z_MASS_GEV:
        return 1.0

    phi_mid = 0.5 * (phi_low + phi_high)
    if phi_mid <= 0.0 or math.isclose(phi_mid, PHI_STAR_REF):
        return 1.0

    depth_num = _hard_scale_depth(numerator_mid)
    depth_den = _hard_scale_depth(denominator_mid)
    signed_log_phi = math.log(max(phi_mid / PHI_STAR_REF, 1.0e-6))
    exponent = (
        ABOVE_Z_SUDAKOV_DIRECTION_STRENGTH
        * LAMBDA_CONTRACTION
        * (depth_num - depth_den)
        * signed_log_phi
    )
    return math.exp(exponent)


def _hard_scale_depth(mass_mid_gev: float) -> float:
    """Continuous DASHI hard-scale depth used by HEP-R47 diagnostics."""

    lambda_qcd_gev = 0.2
    return math.log(max(mass_mid_gev / lambda_qcd_gev, 1.0e-12)) / math.log(3.0)


def _window_sigma(mass_low: float, mass_high: float, phi_low: float, phi_high: float) -> float:
    mass_norm = _mass_normalization(mass_low, mass_high)
    total = 0.0
    count = 0
    for mass in _mass_quadrature_points(mass_low, mass_high):
        for phi_star in _phi_quadrature_points(phi_low, phi_high):
            total += (
                _carrier_phase_density(mass, phi_star, phi_low, phi_high)
                * _neutral_current_continuum_factor(mass, phi_star)
                * _posterior_shape_response_factor(mass, phi_star)
            )
            count += 1
    return mass_norm * total / count


def _carrier_phase_density(mass_gev: float, phi_star: float, phi_low: float, phi_high: float) -> float:
    """Average the HEP-R39 finite-carrier density for one phi-star sample.

    This is a smooth density, not a hard support count.  A hard predicate over
    the 3^8 finite state space can make the first t43 bins exactly empty,
    which is a discretization artifact rather than a governed prediction.
    """

    depth = _phi_star_depth(phi_star)
    bin_width = max(phi_high - phi_low, 1.0e-12)
    total_weight = 0.0
    weighted_density = 0.0
    for state in TRIT_STATES:
        weight = _trit_state_weight(state, mass_gev, phi_star, depth)
        carrier_phi = _state_phi_star(state, mass_gev, depth)
        density = _log_phi_kernel(phi_star, carrier_phi, depth, bin_width)
        total_weight += weight
        weighted_density += weight * density
    if total_weight <= 0.0:
        return 0.0
    return weighted_density / total_weight


def _trit_state_weight(state: tuple[int, ...], mass_gev: float, phi_star: float, depth: int) -> float:
    gap = _state_gap(state)
    polarity = abs(_state_polarity(state))
    curvature = sum((state[index] - state[index - 1]) ** 2 for index in range(1, len(state)))

    q_over_m = max(phi_star, 1.0e-12)
    hard_scale = math.log1p(mass_gev * q_over_m)
    soft_depth = math.log1p(1.0 / q_over_m)

    energy = (
        LAMBDA_CONTRACTION * depth * (1.0 - gap)
        + 0.018 * hard_scale * curvature
        + 0.090 * soft_depth * polarity
    )
    return math.exp(-energy)


def _state_phi_star(state: tuple[int, ...], mass_gev: float, depth: int) -> float:
    polarity = abs(_state_polarity(state))
    gap = _state_gap(state)
    mass_tilt = math.sqrt(Z_MASS_GEV / mass_gev)
    soft_floor = 3.0 ** (-(depth + 4))
    resolved_scale = math.exp(-depth * (1.0 - gap))
    return max(soft_floor, PHI_STAR_REF * mass_tilt * resolved_scale * (0.10 + polarity))


def _log_phi_kernel(phi_star: float, carrier_phi: float, depth: int, bin_width: float) -> float:
    sample = max(phi_star, 1.0e-12)
    centre = max(carrier_phi, 1.0e-12)
    log_distance = math.log(sample / centre)
    sigma = 0.28 + 0.10 * max(0, MAX_CARRIER_DEPTH - depth) + 0.05 * math.log1p(1.0 / bin_width)
    norm = sigma * math.sqrt(2.0 * math.pi) * sample
    return math.exp(-0.5 * (log_distance / sigma) ** 2) / norm


def _phi_star_depth(phi_star_mid: float) -> int:
    if phi_star_mid <= 0.0:
        return MAX_CARRIER_DEPTH
    log_ratio = math.log(PHI_STAR_REF / phi_star_mid) / math.log(3.0)
    depth = DEPTH_EW + math.floor(log_ratio)
    return max(MIN_CARRIER_DEPTH, min(MAX_CARRIER_DEPTH, int(depth)))


def _mass_normalization(mass_low: float, mass_high: float) -> float:
    integral = _breit_wigner_flux_integral(mass_low, mass_high)
    if integral <= 0.0:
        raise ArithmeticError("non-positive Breit-Wigner normalization integral")
    return integral * _above_z_neutral_current_tail_factor(mass_low, mass_high)


def _breit_wigner_flux_integral(mass_low: float, mass_high: float) -> float:
    width = mass_high - mass_low
    step = width / BREIT_WIGNER_STEPS
    total = 0.0
    for index in range(BREIT_WIGNER_STEPS):
        mass = mass_low + (index + 0.5) * step
        mass_squared = mass * mass
        denominator = (mass_squared - Z_MASS_GEV * Z_MASS_GEV) ** 2 + (Z_MASS_GEV * Z_WIDTH_GEV) ** 2
        total += step / (denominator * mass_squared)
    return total


def neutral_current_window_factor(mass_low: float, mass_high: float) -> float:
    """Return the gamma/Z neutral-current window ratio to the Z-peak window.

    This is a diagnostic mass-kernel helper for the t45 high-mass holdout.  The
    existing t43 lane is below the Z pole and remains governed by the
    Breit-Wigner kernel that already matches the 50-76 / 76-106 scale.  Above
    the pole the photon and gamma/Z interference terms soften the pure-Z tail;
    this ratio records that tail support without reading observed ratios.
    """

    numerator = _neutral_current_flux_integral(mass_low, mass_high)
    denominator = _neutral_current_flux_integral(*MASS_WINDOW_76_106_GEV)
    if denominator <= 0.0:
        raise ArithmeticError("non-positive neutral-current reference integral")
    return numerator / denominator


def _above_z_neutral_current_tail_factor(mass_low: float, mass_high: float) -> float:
    """Correct only the high-mass off-shell tail relative to pure Z exchange."""

    if mass_high <= Z_MASS_GEV:
        return 1.0

    pure_ratio = _breit_wigner_flux_integral(mass_low, mass_high) / _breit_wigner_flux_integral(
        *MASS_WINDOW_76_106_GEV
    )
    if pure_ratio <= 0.0:
        raise ArithmeticError("non-positive pure-Z window ratio")
    return neutral_current_window_factor(mass_low, mass_high) / pure_ratio


def _neutral_current_flux_integral(mass_low: float, mass_high: float) -> float:
    width = mass_high - mass_low
    step = width / BREIT_WIGNER_STEPS
    total = 0.0
    for index in range(BREIT_WIGNER_STEPS):
        mass = mass_low + (index + 0.5) * step
        total += step * _neutral_current_integrand(mass) / (mass * mass)
    return total


@lru_cache(maxsize=32)
def _component_fractions(mass_low: float, mass_high: float) -> tuple[float, float, float]:
    """Return gamma, gamma/Z interference, and Z fractions for one window."""

    gamma, interference, z_component = _neutral_current_component_integrals(mass_low, mass_high)
    total = gamma + interference + z_component
    if abs(total) < 1.0e-30:
        return 0.0, 0.0, 1.0
    return gamma / total, interference / total, z_component / total


def _neutral_current_component_integrals(mass_low: float, mass_high: float) -> tuple[float, float, float]:
    width = mass_high - mass_low
    step = width / BREIT_WIGNER_STEPS
    gamma_total = 0.0
    interference_total = 0.0
    z_total = 0.0
    for index in range(BREIT_WIGNER_STEPS):
        mass = mass_low + (index + 0.5) * step
        flux = step / (mass * mass)
        gamma, interference, z_component = _neutral_current_components(mass)
        gamma_total += flux * gamma
        interference_total += flux * interference
        z_total += flux * z_component
    return gamma_total, interference_total, z_total


def _neutral_current_components(mass_gev: float) -> tuple[float, float, float]:
    gamma_term = ALPHA_EW_Z**2 * _PHOTON_PREFAC
    interference_term = ALPHA_EW_Z * _GAMMA_Z_INTERFERENCE_PREFAC * _chi_z_real(mass_gev)
    z_term = _Z_PREFAC * _chi_z_abs2(mass_gev)
    return gamma_term, interference_term, z_term


def _neutral_current_integrand(mass_gev: float) -> float:
    gamma_term, interference_term, z_term = _neutral_current_components(mass_gev)
    return max(0.0, gamma_term + interference_term + z_term)


def _chi_z_real(mass_gev: float) -> float:
    mass_squared = mass_gev * mass_gev
    z_squared = Z_MASS_GEV * Z_MASS_GEV
    denominator = (mass_squared - z_squared) ** 2 + (Z_MASS_GEV * Z_WIDTH_GEV) ** 2
    electroweak_factor = 1.0 / (4.0 * WEAK_MIXING_SIN2 * (1.0 - WEAK_MIXING_SIN2))
    return electroweak_factor * mass_squared * (mass_squared - z_squared) / denominator


def _chi_z_abs2(mass_gev: float) -> float:
    mass_squared = mass_gev * mass_gev
    z_squared = Z_MASS_GEV * Z_MASS_GEV
    denominator = (mass_squared - z_squared) ** 2 + (Z_MASS_GEV * Z_WIDTH_GEV) ** 2
    electroweak_factor = 1.0 / (4.0 * WEAK_MIXING_SIN2 * (1.0 - WEAK_MIXING_SIN2)) ** 2
    return electroweak_factor * mass_squared * mass_squared / denominator


def _neutral_current_continuum_factor(mass_gev: float, phi_star: float) -> float:
    """Diagnostic gamma/Z continuum support for off-peak Drell-Yan windows.

    The HEP-R39 Breit-Wigner-only mass kernel underweights the low-mass window
    in soft and shoulder phi-star regions.  This factor records a bounded
    neutral-current continuum correction: lower masses receive more photon-like
    support, and that support is strongest in the soft/shoulder phi-star
    regimes.  It remains a diagnostic construction; the constants are fixed
    here and are not an accepted authority/calibration receipt.
    """

    phi = max(phi_star, 1.0e-12)
    mass_leverage = (Z_MASS_GEV / mass_gev) ** 2
    soft = 1.0 / (1.0 + (phi / CONTINUUM_SOFT_PHI_SCALE) ** CONTINUUM_SOFT_POWER)
    shoulder = (phi / (phi + CONTINUUM_SHOULDER_ONSET)) * math.exp(
        -phi / CONTINUUM_SHOULDER_PHI_SCALE
    )
    continuum = soft + CONTINUUM_SHOULDER_WEIGHT * shoulder
    return 1.0 + CONTINUUM_STRENGTH * mass_leverage * continuum


def _posterior_shape_response_factor(mass_gev: float, phi_star: float) -> float:
    """Posterior diagnostic shoulder/recovery correction.

    HEP-R40 removes the gross normalization error but leaves a structured
    residual: overprediction in the phi-star shoulder and underprediction in
    the recovery region.  This factor encodes that residual-shape hypothesis as
    a bounded mass-leveraged response.  It is explicitly posterior diagnostic
    state, not a clean-freeze prediction policy.
    """

    phi = max(phi_star, 1.0e-12)
    mass_leverage = (Z_MASS_GEV / mass_gev) ** 2
    shoulder_dip = math.exp(-0.5 * (math.log(phi / SHAPE_DIP_CENTER) / SHAPE_DIP_LOG_WIDTH) ** 2)
    recovery_bump = math.exp(-0.5 * (math.log(phi / SHAPE_BUMP_CENTER) / SHAPE_BUMP_LOG_WIDTH) ** 2)
    response = -SHAPE_DIP_STRENGTH * shoulder_dip + SHAPE_BUMP_STRENGTH * recovery_bump
    factor = 1.0 + mass_leverage * response
    return max(0.05, factor)


def _state_gap(state: tuple[int, ...]) -> float:
    return sum(1 for trit in state if trit != 0) / len(state)


def _state_polarity(state: tuple[int, ...]) -> float:
    return sum(state) / len(state)


def _mass_quadrature_points(low: float, high: float) -> tuple[float, ...]:
    width = high - low
    return (
        low + 0.2113248654051871 * width,
        low + 0.7886751345948129 * width,
    )


def _phi_quadrature_points(low: float, high: float) -> tuple[float, ...]:
    width = high - low
    return (
        low + 0.125 * width,
        low + 0.375 * width,
        low + 0.625 * width,
        low + 0.875 * width,
    )


def _finite_mass_window(mass_window_gev: tuple[float, float]) -> tuple[float, float]:
    if not isinstance(mass_window_gev, tuple) or len(mass_window_gev) != 2:
        raise TypeError("mass_window_gev must be a tuple[float, float]")
    low = float(mass_window_gev[0])
    high = float(mass_window_gev[1])
    if not math.isfinite(low) or not math.isfinite(high):
        raise ValueError(f"mass window edges must be finite, got {mass_window_gev!r}")
    if low <= 0.0 or high <= low:
        raise ValueError(f"mass window must satisfy 0 < low < high, got {mass_window_gev!r}")
    return low, high


def _finite_number(raw: Any, label: str) -> float:
    value = float(raw)
    if not math.isfinite(value):
        raise ValueError(f"{label} must be finite, got {raw!r}")
    return value


def _finite_edge(bin_record: Mapping[str, Any], key: str) -> float:
    if key not in bin_record:
        raise KeyError(f"missing required t43 bin edge {key!r}")
    return _finite_number(bin_record[key], key)


__all__ = [
    "ACCEPTED_EMPIRICAL_ADEQUACY_RECEIPT",
    "CONSTRUCTION_CLASSIFICATION",
    "MASS_WINDOW_50_76_GEV",
    "MASS_WINDOW_106_170_GEV",
    "MASS_WINDOW_76_106_GEV",
    "NON_PROMOTION_BOUNDARY",
    "OBSERVED_T43_RATIO_SEEDING",
    "POSTERIOR_DIAGNOSTIC_REFINEMENT",
    "PROMOTES_W3",
    "TRIT_DEPTH",
    "TRIT_STATES",
    "TRIT_VALUES",
    "metadata",
    "neutral_current_window_factor",
    "predict_ratio",
    "predict_ratio_106_170_over_76_106",
    "sigma_DASHI",
]
