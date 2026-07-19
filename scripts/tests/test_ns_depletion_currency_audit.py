from __future__ import annotations

from pathlib import Path
import sys

import numpy as np
import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_depletion_currency_audit import (
    CURRENCY_NAMES,
    currency_snapshot,
    direction_turnover_rate,
    integrate_currency_rows,
    projector_turnover_rate,
    validate_currency_rows,
)
from ns_galerkin_coherence_core import exact_alignment_budget
from ns_generate_matched_galerkin_trajectories import triad_excursion_initial_hat


def test_direction_turnover_ignores_parallel_vorticity_growth():
    omega = np.asarray([[[[1.0, 2.0, -3.0]]]])
    omega_dot = 7.0 * omega
    weights = np.ones((1, 1, 1))
    assert direction_turnover_rate(omega, omega_dot, weights, 2.0) == pytest.approx(0.0, abs=1e-14)


def test_projector_tangent_rate_is_nonnegative_and_zero_for_stationary_projector():
    projector_dot = np.zeros((1, 1, 1, 3, 3))
    weights = np.ones((1, 1, 1))
    assert projector_turnover_rate(projector_dot, weights, 3.0) == 0.0
    projector_dot[..., 0, 1] = 2.0
    assert projector_turnover_rate(projector_dot, weights, 2.0) == pytest.approx(1.0)


def row(trajectory: str, index: int, cutoff: int, time: float, gamma: float, values: dict[str, float]):
    return {
        "trajectory_id": trajectory,
        "checkpoint_index": index,
        "time": time,
        "cutoff": cutoff,
        "gamma": gamma,
        "tight": True,
        "parabolic_rate": 10.0,
        "currencies": values,
        "positive_remainder": 1.0 + time,
    }


def values(direction: float, projector: float, cross: float, middle: float) -> dict[str, float]:
    return {
        "direction_turnover": direction,
        "spectral_projector_turnover": projector,
        "cross_shell_coherence_activity": cross,
        "middle_simple_spectrum_alignment": middle,
    }


def test_currency_validation_is_nonvacuous_and_branch_specific():
    rows = [
        row("train", 0, 32, 0.0, 0.8, values(0.02, 0.0, 0.03, 0.0)),
        row("train", 1, 48, 0.1, 0.8, values(0.02, 0.0, 0.03, 0.0)),
        row("holdout", 2, 64, 0.0, 0.8, values(0.02, 0.0, 0.03, 0.0)),
    ]
    result = validate_currency_rows(rows, (0.5,), (0.01,), (32, 48, 64), ("holdout",))
    assert result["matched_cutoff_set_complete"] is True
    assert result["heldout_nonvacuous_excursion_coverage"] is True
    assert result["currency_has_nonvacuous_heldout_candidate"]["direction_turnover"] is True
    assert result["currency_has_nonvacuous_heldout_candidate"]["cross_shell_coherence_activity"] is True
    assert result["currency_has_nonvacuous_heldout_candidate"]["middle_simple_spectrum_alignment"] is False


def test_no_excursion_never_counts_as_a_currency_pass():
    rows = [
        row("train", 0, 32, 0.0, 0.2, values(10.0, 10.0, 10.0, 10.0)),
        row("holdout", 1, 64, 0.0, 0.2, values(10.0, 10.0, 10.0, 10.0)),
    ]
    result = validate_currency_rows(rows, (0.5,), (0.01,), (32, 64), ("holdout",))
    assert result["heldout_nonvacuous_excursion_coverage"] is False
    assert result["any_candidate_currency_passes_sampled_heldout_gate"] is False


def test_interval_audit_accumulates_cross_shell_currency_without_terminal_duration():
    rows = [
        row("x", 0, 32, 0.0, 0.8, values(1.0, 1.0, 2.0, 1.0)),
        row("x", 1, 32, 0.1, 0.8, values(1.0, 1.0, 4.0, 1.0)),
    ]
    result = integrate_currency_rows(rows, (0.5,))[0]
    assert len(result["intervals"]) == 1
    assert result["cross_shell_cumulative_budget"] == pytest.approx(3.0)
    dangerous = result["certainly_dangerous_integrals"]["0.5"]
    assert dangerous["cross_shell_coherence_activity"]["integrated_currency"] == pytest.approx(3.0)


def test_positive_transfer_triad_produces_finite_nonnegative_currencies():
    raw = triad_excursion_initial_hat(16, 0.1, 0.25)
    exact = exact_alignment_budget(raw, 0.01, 2)
    snapshot = currency_snapshot(raw, 0.01, 2, exact)
    assert tuple(snapshot["currency_values"]) == CURRENCY_NAMES
    assert all(np.isfinite(value) and value >= 0.0 for value in snapshot["currency_values"].values())
    assert snapshot["authority"]["analytic_depletion_identification"] is False
    assert snapshot["authority"]["clay_authority"] is False
