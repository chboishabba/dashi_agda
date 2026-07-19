from __future__ import annotations

from pathlib import Path
import sys

import numpy as np
import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_bounded_turnover_potential_audit import (  # noqa: E402
    alignment_potential_derivative,
    bounded_potential_snapshot,
    integrate_bounded_potential_rows,
    validate_signed_escape,
)
from ns_generate_matched_galerkin_trajectories import (  # noqa: E402
    triad_excursion_initial_hat,
)


def test_unsigned_direction_motion_need_not_change_bounded_potential() -> None:
    omega = np.zeros((1, 1, 1, 3), dtype=float)
    omega[..., 0] = 1.0
    omega_dot = np.zeros_like(omega)
    omega_dot[..., 1] = 1.0
    projector = np.broadcast_to(np.eye(3) / 3.0, (1, 1, 1, 3, 3)).copy()
    projector_dot = np.zeros_like(projector)
    result = alignment_potential_derivative(
        omega, omega_dot, projector, projector_dot
    )
    assert result["potential"] == pytest.approx(1.0 / 3.0)
    assert result["direction_motion"] == pytest.approx(0.0, abs=1.0e-14)
    assert result["quotient_derivative"] == pytest.approx(0.0, abs=1.0e-14)
    assert result["decomposition_residual"] < 1.0e-14


def test_exact_triad_potential_decomposition_closes() -> None:
    raw = triad_excursion_initial_hat(16, 0.1, 0.25)
    result = bounded_potential_snapshot(raw, 0.01, 2)
    assert 0.0 <= result["soft_alignment_potential"] <= 1.0
    direct = result["direct_signed_derivative"]
    assert direct["decomposition_residual"] < 1.0e-8
    assert max(result["component_sum_residuals"].values()) < 1.0e-8
    assert result["authority"]["danger_forces_signed_escape"] is False


def test_one_sided_interval_balance_and_terminal_duration() -> None:
    rows = [
        {
            "trajectory_id": "x",
            "checkpoint_index": 0,
            "time": 0.0,
            "parabolic_rate": 1.0,
            "potential": 0.8,
            "potential_derivative": -0.1,
            "depletion": 0.1,
            "replenishment": 0.0,
            "gamma": 0.8,
        },
        {
            "trajectory_id": "x",
            "checkpoint_index": 1,
            "time": 1.0,
            "parabolic_rate": 1.0,
            "potential": 0.7,
            "potential_derivative": -0.1,
            "depletion": 0.1,
            "replenishment": 0.0,
            "gamma": 0.8,
        },
    ]
    result = integrate_bounded_potential_rows(rows, (0.5,))[0]
    assert len(result["intervals"]) == 1
    assert result["integrated_depletion"] == pytest.approx(0.1)
    assert result["quadrature_allowance"] == pytest.approx(0.0, abs=1.0e-14)
    assert result["bounded_potential_budget_holds_with_quadrature_allowance"] is True
    assert result["certainly_dangerous_parabolic_residence"]["0.5"] == pytest.approx(1.0)


def _validation_row(trajectory: str, cutoff: int, escape: float) -> dict:
    return {
        "trajectory_id": trajectory,
        "checkpoint_index": cutoff,
        "time": 0.0,
        "cutoff": cutoff,
        "gamma": 0.8,
        "tight": True,
        "currencies": {
            "net_alignment_escape": escape,
            "direction_alignment_escape": escape,
            "projector_alignment_escape": 0.0,
            "mechanism_escape_sum": escape,
        },
    }


def test_signed_escape_validation_is_branch_specific_and_nonvacuous() -> None:
    rows = [
        _validation_row("train-32", 32, 0.2),
        _validation_row("train-48", 48, 0.2),
        _validation_row("holdout-64", 64, 0.2),
    ]
    result = validate_signed_escape(
        rows, (0.5,), (0.1,), (32, 48, 64), ("holdout-64",)
    )
    assert result["matched_cutoff_set_complete"] is True
    assert result["currency_has_nonvacuous_heldout_signed_escape"]["net_alignment_escape"] is True
    assert result["currency_has_nonvacuous_heldout_signed_escape"]["projector_alignment_escape"] is False
