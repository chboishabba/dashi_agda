from __future__ import annotations

from pathlib import Path
import sys

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_triad_gamma_gap_core import (  # noqa: E402
    Constraints,
    Mode,
    Problem,
    SearchConfig,
    Triad,
    evaluate_profile,
)
from ns_triad_gamma_gap_search import audit_problem, window_rows  # noqa: E402


def config(**overrides):
    values = dict(
        target_eta=0.05,
        random_samples=0,
        local_steps=0,
        seeds=(0,),
        zero_eps=1.0e-12,
        constraints=Constraints(),
        cancellation_cap=0.75,
        envelope_cap=0.75,
        window_sizes=(2,),
    )
    values.update(overrides)
    return SearchConfig(**values)


def basic_problem(coefficients=(2.0, -1.0), profiles=()):
    return Problem(
        problem_id="basic",
        viscosity=0.5,
        modes=(
            Mode((1, 0, 0), 1.0),
            Mode((0, 1, 0), 1.0),
            Mode((1, 1, 0), 2.0),
        ),
        triads=tuple(Triad(0, 1, 2, coefficient) for coefficient in coefficients),
        profiles=tuple(profiles),
    )


def test_orbit_quotient_cancels_before_absolute_envelope():
    row = evaluate_profile(
        basic_problem((2.0, -1.0)),
        [1 / 3, 1 / 3, 1 / 3],
        config(),
        profile_id="p",
        source="test",
    )
    amplitude_product = (1 / 3) ** 1.5
    assert np.isclose(row["q"], amplitude_product)
    assert np.isclose(row["a"], amplitude_product)
    assert row["orbit_block_count"] == 1


def test_finite_gamma_product_identity_is_machine_zero():
    row = evaluate_profile(
        basic_problem((2.0, -1.0)),
        [0.2, 0.3, 0.5],
        config(),
        profile_id="p",
        source="test",
    )
    assert row["gamma"] is not None
    assert np.isclose(row["gamma"], row["product"])
    assert row["identity_residual"] < 1.0e-14


def test_same_orbit_opposite_contributions_deplete_exactly():
    row = evaluate_profile(
        basic_problem((1.0, -1.0)),
        [1 / 3, 1 / 3, 1 / 3],
        config(),
        profile_id="p",
        source="test",
    )
    assert np.isclose(row["q"], 0.0)
    assert np.isclose(row["a"], 0.0)
    assert np.isclose(row["gamma"], 0.0)


def test_duration_weighted_windows_match_discrete_integral():
    rows = [
        {
            "profile_id": "a",
            "trajectory_id": "t",
            "cutoff": 4,
            "time": 0.0,
            "duration": 1.0,
            "gamma": 0.2,
        },
        {
            "profile_id": "b",
            "trajectory_id": "t",
            "cutoff": 4,
            "time": 1.0,
            "duration": 3.0,
            "gamma": 0.6,
        },
    ]
    windows = window_rows(rows, (2,), target_eta=0.1)
    whole = next(row for row in windows if row["window_size"] == 2)
    assert np.isclose(whole["integrated_gamma"], 2.0)
    assert np.isclose(whole["interval_length"], 4.0)
    assert np.isclose(whole["average_gamma"], 0.5)


def test_adversarial_search_includes_single_triad_extremizer_seed():
    problem = Problem(
        problem_id="four-mode",
        viscosity=0.5,
        modes=(
            Mode((1, 0, 0), 1.0),
            Mode((0, 1, 0), 1.0),
            Mode((1, 1, 0), 2.0),
            Mode((0, 0, 1), 1.0),
        ),
        triads=(Triad(0, 1, 2, 20.0),),
    )
    result = audit_problem(problem, config(target_eta=0.5))
    assert result["worst_profile"] is not None
    assert result["worst_profile"]["profile_id"].startswith("triad-seed")
    assert result["target_counterexample_count"] >= 1
    assert result["no_counterexample_sampled"] is False
