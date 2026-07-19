from __future__ import annotations

from pathlib import Path
import sys

import numpy as np
import pytest


SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_packet_coherence_budget_audit import (  # noqa: E402
    BudgetPoint,
    audit,
    budget_intervals,
    eigenframe_metrics,
)


def test_eigenframe_identity_and_branches_partition() -> None:
    grad = np.zeros((2, 1, 1, 3, 3), dtype=float)
    grad[..., 0, 0] = 2.0
    grad[..., 1, 1] = 0.5
    grad[..., 2, 2] = -2.5
    grad[..., 1, 0] = 1.0
    grad[..., 0, 1] = -1.0
    pressure = np.zeros_like(grad)
    metrics = eigenframe_metrics(
        grad,
        pressure,
        nu=0.1,
        target_shell=1,
        middle_alpha_threshold=0.2,
        gap_relative_floor=1.0e-6,
    )
    assert metrics["eigenframe_stretching_identity_max_residual"] < 1.0e-12
    assert metrics["alignment_partition_residual"] < 1.0e-12
    assert sum(
        metrics["branch_fractions"][key]
        for key in (
            "biaxial_lambda2_nonpositive",
            "lambda2_positive_middle_alignment_small",
            "lambda2_positive_middle_alignment_substantial",
        )
    ) == pytest.approx(1.0)


def test_rank_two_gradient_has_zero_planarity_defect() -> None:
    grad = np.zeros((1, 1, 1, 3, 3), dtype=float)
    grad[..., 0, 0] = 1.0
    grad[..., 1, 1] = -1.0
    grad[..., 1, 0] = 1.0
    grad[..., 0, 1] = -1.0
    pressure = np.zeros_like(grad)
    metrics = eigenframe_metrics(
        grad,
        pressure,
        nu=0.1,
        target_shell=1,
        middle_alpha_threshold=0.2,
        gap_relative_floor=1.0e-6,
    )
    assert metrics["quasi_2d_planarity_defect"]["weighted_mean"] == pytest.approx(0.0)
    assert metrics["quasi_2d_planarity_defect"]["near_columnar_enstrophy_fraction_1e-6"] == pytest.approx(1.0)


def test_end_to_end_columnar_checkpoint(tmp_path: Path) -> None:
    n = 8
    coordinate = 2.0 * np.pi * np.arange(n) / n
    _z, y, x = np.meshgrid(coordinate, coordinate, coordinate, indexing="ij")
    velocity = np.zeros((n, n, n, 3), dtype=float)
    velocity[..., 0] = np.sin(y)
    velocity[..., 1] = np.sin(x)
    raw_hat = np.fft.fftn(velocity, axes=(0, 1, 2))
    state = tmp_path / "state.npz"
    np.savez(state, raw_hat=raw_hat, nu=0.01)

    residence = {
        "checkpoints": [
            {
                "checkpoint_index": 0,
                "source_state": str(state),
                "trajectory_id": "synthetic",
                "time": 0.0,
                "parabolic_duration": 0.1,
                "target_shell": 0,
                "gamma": 0.0,
                "packet_tight": True,
                "packet_geometry": {"local_shell_mass_fraction": 1.0},
            }
        ]
    }
    result = audit(
        residence,
        (0.5,),
        (0.1,),
        middle_alpha_threshold=0.2,
        gap_relative_floor=1.0e-6,
        pressure_coefficient=1.0,
        tail_coefficient=1.0,
        middle_coefficient=1.0,
        allow_missing_state=False,
    )
    metrics = result["checkpoints"][0]["coherence_metrics"]
    assert metrics is not None
    assert 0.0 <= metrics["coherence_budget_A1"] <= 1.0
    assert metrics["quasi_2d_planarity_defect"]["weighted_mean"] < 1.0e-12
    assert metrics["pressure_hessian"]["trace_free_projection_weighted_trace_residual"] < 1.0e-10
    assert result["authority"]["promoted"] is False
    assert result["uniform_candidate_tested_across_multiple_cutoffs"] is False


def test_budget_interval_candidate_is_fail_closed() -> None:
    points = [
        BudgetPoint("x", 0, 8, 1, 0.0, 0.5, 1.0, True, 0.1, 0.8, 0.2, 0.3),
        BudgetPoint("x", 1, 8, 1, 0.5, 0.5, 0.0, True, 0.1, 0.7, 0.2, 0.3),
    ]
    result = budget_intervals(
        points,
        (0.9,),
        (0.1,),
        pressure_coefficient=1.0,
        tail_coefficient=1.0,
        middle_coefficient=1.0,
    )
    parameter = result[0]["parameter_audits"][0]
    assert parameter["tested_interval_count"] == 1
    assert parameter["dangerous_parabolic_residence"] == pytest.approx(0.5)
