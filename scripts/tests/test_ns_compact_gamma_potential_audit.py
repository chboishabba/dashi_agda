from __future__ import annotations

from pathlib import Path
import sys

import numpy as np
import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_compact_gamma_potential_audit import (  # noqa: E402
    compact_gamma_snapshot,
    compact_state_values,
    validate_compact_escape,
)
from ns_generate_matched_galerkin_trajectories import (  # noqa: E402
    triad_excursion_initial_hat,
)


def test_positive_triad_compact_relation_and_exact_derivative() -> None:
    raw = triad_excursion_initial_hat(16, 0.1, 0.25)
    result = compact_gamma_snapshot(raw, 0.01, 2)
    gamma = result["gamma"]
    compact = result["compact_gamma_potential_B"]
    assert result["positive_part_branch"] == "strict_positive_transfer"
    assert gamma > 0.5
    assert compact == pytest.approx(gamma / (1.0 + gamma), rel=1.0e-12)
    assert result["compact_relation_residual"] < 1.0e-12
    residuals = [
        value for value in result["component_sum_residuals"].values()
        if value is not None
    ]
    assert residuals and max(residuals) < 1.0e-8
    assert result["state_rhs_component_sum_max_residual"] < 1.0e-8
    finite = result["finite_difference_check"]["residual"]
    assert finite is not None and finite < 1.0e-6


def test_gamma_threshold_is_compact_level_threshold() -> None:
    raw = triad_excursion_initial_hat(16, 0.1, 0.25)
    result = compact_state_values(raw, 0.01, 2)
    for threshold in (0.1, 0.5, 0.9, 1.0):
        compact_threshold = threshold / (1.0 + threshold)
        assert (result["gamma"] >= threshold) == (
            result["compact_gamma_potential_B"] >= compact_threshold
        )


def test_zero_transfer_positive_part_kink_fails_closed() -> None:
    n = 16
    raw = np.zeros((n, n, n, 3), dtype=np.complex128)
    scale = float(n ** 3)
    mode = (3, 3, 2)
    vector = np.asarray((6.0, 6.0, -18.0)) / 11.0
    x, y, z = mode
    raw[z % n, y % n, x % n] = scale * vector
    raw[(-z) % n, (-y) % n, (-x) % n] = scale * vector
    result = compact_gamma_snapshot(raw, 0.01, 2)
    assert result["positive_part_branch"] == "positive_part_kink_unresolved"
    assert result["compact_derivative_parabolic"] is None
    assert all(
        value is None
        for value in result["candidate_signed_escape_currencies"].values()
    )
    assert result["authority"]["positive_part_kink_failed_closed"] is True


def _row(trajectory: str, cutoff: int, escape: float) -> dict:
    return {
        "trajectory_id": trajectory,
        "checkpoint_index": cutoff,
        "time": 0.0,
        "cutoff": cutoff,
        "gamma": 0.8,
        "potential": 0.8 / 1.8,
        "tight": True,
        "branch_resolved": True,
        "currencies": {
            "net_compact_gamma_escape": escape,
            "target_nonlinear_escape": escape,
            "off_packet_nonlinear_escape": 0.0,
            "viscous_escape": 0.0,
            "mechanism_escape_sum": escape,
        },
    }


def test_compact_escape_validation_is_nonvacuous_and_branch_specific() -> None:
    rows = [
        _row("train-32", 32, 0.2),
        _row("train-48", 48, 0.2),
        _row("holdout-64", 64, 0.2),
    ]
    result = validate_compact_escape(
        rows, (0.5,), (0.1,), (32, 48, 64), ("holdout-64",)
    )
    assert result["matched_cutoff_set_complete"] is True
    assert result["currency_has_nonvacuous_heldout_compact_escape"][
        "net_compact_gamma_escape"
    ] is True
    assert result["currency_has_nonvacuous_heldout_compact_escape"][
        "viscous_escape"
    ] is False
    assert all(
        audit["gamma_compact_level_equivalence"]
        for audit in result["parameter_audits"]
    )
