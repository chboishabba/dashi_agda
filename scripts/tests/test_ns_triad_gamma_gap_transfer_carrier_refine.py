from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

import numpy as np


SCRIPT = Path(__file__).resolve().parents[1] / "ns_triad_gamma_gap_transfer_carrier_refine.py"
SPEC = importlib.util.spec_from_file_location("gamma_refine", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def _problem() -> dict:
    return {
        "problem_id": "refine-regression",
        "viscosity": 1.0,
        "modes": [
            {"wavevector": [1, 0, 0]},
            {"wavevector": [0, 1, 0]},
            {"wavevector": [1, 1, 0]},
            {"wavevector": [0, 0, 1]},
            {"wavevector": [1, 1, 1]},
            {"wavevector": [1, 0, 1]},
        ],
        "triads": [
            {"left": 0, "right": 1, "out": 2, "coefficient": 10.0},
            {"left": 2, "right": 3, "out": 4, "coefficient": 1.0},
            {"left": 0, "right": 3, "out": 5, "coefficient": 0.1},
        ],
        "profiles": [
            {
                "profile_id": "t0",
                "probability": [0.20, 0.20, 0.20, 0.15, 0.15, 0.10],
            },
            {
                "profile_id": "t1",
                "probability": [0.25, 0.15, 0.20, 0.10, 0.20, 0.10],
            },
        ],
    }


def test_partner_closure_adds_missing_output() -> None:
    problem = _problem()
    modes, triads = MODULE._validate_problem(problem)
    probability = MODULE._probability(problem["profiles"][0], len(modes), 1.0e-15)
    magnitudes = MODULE._triad_transfer_magnitudes(triads, probability)
    selected, seeds, _ = MODULE._seed_modes(triads, magnitudes, 0.80, 1.0e-15)
    assert seeds == [0]
    assert selected == {0, 1, 2}
    closed, _, converged = MODULE._partner_close(selected, triads, 8)
    assert converged is True
    assert 4 not in closed
    closed_from_two, _, _ = MODULE._partner_close({0, 1, 2, 3}, triads, 8)
    assert 4 in closed_from_two
    assert 5 in closed_from_two


def test_reduced_profiles_are_renormalized_and_authority_false() -> None:
    reduced = MODULE._reduce_problem(
        _problem(), profile_id="t0", capture=0.95, max_rounds=8, zero_eps=1.0e-15
    )
    receipt = reduced["carrier_refinement"]
    assert receipt["candidate_only"] is True
    assert receipt["theorem_authority"] is False
    assert receipt["clay_authority"] is False
    assert receipt["closure_converged"] is True
    assert receipt["transfer_capture_fraction"] >= 0.95
    assert receipt["selected_mode_count_after_closure"] >= receipt["selected_mode_count_before_closure"]
    for profile in reduced["profiles"]:
        assert np.isclose(sum(profile["probability"]), 1.0)
        assert 0.0 < profile["source_probability_mass_retained"] <= 1.0


def test_invalid_triad_geometry_fails_closed() -> None:
    problem = _problem()
    problem["triads"][0]["out"] = 3
    try:
        MODULE._validate_problem(problem)
    except ValueError as exc:
        assert "p+q=k" in str(exc)
    else:
        raise AssertionError("invalid triad geometry was accepted")
