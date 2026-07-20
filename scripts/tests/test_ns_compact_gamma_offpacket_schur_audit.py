from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_compact_gamma_offpacket_schur_audit import (  # noqa: E402
    candidate_metrics,
    evaluate_candidate,
    fit_candidate,
    off_response,
    weighted_norm_from_components,
)
from ns_compact_gamma_potential_audit import _state_geometry  # noqa: E402
from ns_generate_matched_galerkin_trajectories import (  # noqa: E402
    triad_excursion_initial_hat,
)


def _response(off: float, escape: float, near: float, tail: float) -> dict:
    # The signed class contributions reconstruct the declared full response.
    assert math.isclose(near + tail, off)
    return {
        "resolved": True,
        "off_derivative": off,
        "escape_supply": escape,
        "shell_components": [
            {
                "shell_offset": 0,
                "off_derivative_contribution": near,
                "xk_energy": 1.0,
                "xk_angular_moment_1": 0.2,
                "xk_angular_moment_2": 0.04,
            },
            {
                "shell_offset": 3,
                "off_derivative_contribution": tail,
                "xk_energy": 0.25,
                "xk_angular_moment_1": 0.1,
                "xk_angular_moment_2": 0.04,
            },
        ],
    }


def _row(response: dict, profile: str = "p") -> dict:
    return {
        "profile_id": profile,
        "center_profile_id": "c",
        "cutoff": 16,
        "target_shell": 2,
        "parabolic_time": 0.0,
        "path_parameter": 0.5,
        "tangent_kind": "path",
        "response": response,
    }


def test_zero_weights_recover_xk_norm() -> None:
    response = _response(0.4, 2.0, 0.3, 0.1)
    norm = weighted_norm_from_components(
        response["shell_components"], shell_exponent=0.0, angular_eta=0.0
    )
    assert norm == pytest.approx(math.sqrt(1.25))
    weighted = weighted_norm_from_components(
        response["shell_components"], shell_exponent=0.5, angular_eta=1.0
    )
    assert weighted > norm


def test_fit_and_evaluate_near_plus_tail_bound() -> None:
    calibration = [_row(_response(0.4, 2.0, 0.3, 0.1))]
    candidate = fit_candidate(
        calibration,
        shell_exponent=0.0,
        angular_eta=0.0,
        tail_radius=1,
        slack=0.2,
    )
    assert candidate["finite_candidate"] is True
    heldout = [_row(_response(0.45, 2.0, 0.32, 0.13), "h")]
    result = evaluate_candidate(heldout, candidate)
    assert result["sampled_offpacket_schur_split_survives"] is True
    assert result["minimum_full_split_margin"] >= 0.0


def test_unresolved_response_fails_closed() -> None:
    row = _row({"resolved": False, "reason": "positive-transfer-branch"})
    candidate = fit_candidate(
        [row],
        shell_exponent=0.0,
        angular_eta=0.0,
        tail_radius=1,
        slack=0.1,
    )
    assert candidate["finite_candidate"] is False
    result = evaluate_candidate([row], candidate)
    assert result["unresolved_row_count"] == 1
    assert result["sampled_offpacket_schur_split_survives"] is False


def test_exact_shell_split_reconstructs_off_derivative() -> None:
    raw = triad_excursion_initial_hat(16, 0.1, 0.25)
    geometry = _state_geometry(raw, 0.01, 2)
    result = off_response(raw, geometry["total_rhs_hat"], nu=0.01, shell=2)
    assert result["resolved"] is True
    assert result["shell_components"]
    assert result["shell_derivative_reconstruction_residual"] < 1.0e-8
    assert result["shell_energy_reconstruction_residual"] < 1.0e-10
    finite = result["off_derivative_finite_difference_residual"]
    assert finite is not None and finite < 1.0e-5
    metrics = candidate_metrics(
        result, shell_exponent=0.5, angular_eta=1.0, tail_radius=1
    )
    assert metrics["weighted_norm"] > 0.0
    assert metrics["full_absolute_response"] <= (
        metrics["near_absolute_response"] + metrics["tail_absolute_response"] + 1.0e-9
    )
