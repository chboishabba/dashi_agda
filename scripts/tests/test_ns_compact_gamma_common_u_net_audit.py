from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_compact_gamma_common_u_net_audit import (
    fit_local_oscillation,
    integrate_profile_remainder,
    normalize_packet_energy,
    packet_parameter_grid,
)
from ns_compact_gamma_multitriad_evolved_audit import multitriad_diffuse_hat


def _row(
    time: float,
    potential: float,
    escape: float,
    replenishment: float,
    *,
    dangerous: bool = True,
):
    return {
        "parabolic_time": time,
        "compact_potential": potential,
        "dangerous": dangerous,
        "mechanism_accounting": {
            "escape_supply": escape,
            "replenishment": replenishment,
        },
    }


def _profile(
    profile_id: str,
    feature: list[float],
    remainder: float,
    shell: int = 2,
    triads: int = 2,
):
    return {
        "profile_id": profile_id,
        "target_shell": shell,
        "parameters": {"triad_count": triads},
        "feature": np.asarray(feature, dtype=float),
        "envelope": {"remainder_C_theta": remainder},
    }


def test_integrated_remainder_uses_parabolic_trapezoid():
    rows = [
        _row(0.0, 0.4, 2.0, 1.0),
        _row(0.5, 0.3, 2.0, 0.0),
        _row(1.0, 0.2, 2.0, 2.0),
    ]
    result = integrate_profile_remainder(rows, theta=0.25)
    assert math.isclose(result["remainder_C_theta"], 0.5)
    assert math.isclose(result["member_upper_B0_plus_C"], 0.9)
    assert math.isclose(result["unit_reduced_upper_1_plus_C"], 1.5)


def test_finite_net_fits_calibration_and_checks_holdout():
    centers = [_profile("c", [0.0, 0.0], 0.1)]
    calibration = [_profile("a", [1.0, 0.0], 0.3)]
    holdout = [_profile("h", [0.5, 0.0], 0.19)]
    result = fit_local_oscillation(
        centers, calibration, holdout, slope_slack=0.0
    )
    assert math.isclose(result["fitted_one_sided_remainder_slope"], 0.2)
    assert math.isclose(result["coverage_radius"], 0.5)
    assert math.isclose(result["common_remainder_upper"], 0.2)
    assert result["sampled_finite_net_bound_survives_holdout"] is True


def test_packet_energy_normalization_is_exact_to_roundoff():
    raw, _metadata = multitriad_diffuse_hat(
        16,
        2,
        triad_count=2,
        input_amplitude=0.1,
        target_ratio=2.5,
        satellite_fraction=0.55,
        phase_spread=0.2,
        seed=1,
    )
    normalized, receipt = normalize_packet_energy(raw, 2, 0.86)
    assert normalized.shape == raw.shape
    assert abs(receipt["post_normalization_packet_energy"] - 0.86) < 1.0e-12
    assert receipt["normalization_residual"] < 1.0e-12


def test_parameter_grid_rejects_invalid_satellite_fraction():
    try:
        packet_parameter_grid((2,), (0.0,), (2.5,), (0.0,))
    except ValueError as error:
        assert "satellite fractions" in str(error)
    else:
        raise AssertionError("invalid satellite fraction was accepted")
