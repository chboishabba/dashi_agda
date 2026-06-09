from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint94_uniform_bound_for_all_a_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint94_uniform_bound_for_all_a"
    / "ym_sprint94_uniform_bound_for_all_a_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint94_closes_uniform_bound_only() -> None:
    summary = run_script()

    assert summary["contraction_delta_lower_bound_required"] is True
    assert summary["uniform_bound_for_all_a_closed_in_repo"] is True
    assert summary["wc3_uniform_in_a_derived_in_repo"] is False
    assert summary["uniform_connected_schwinger_decay_derived_in_repo"] is False
    assert summary["continuum_limit_mass_gap_derived_in_repo"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint94_uniform_constants_come_from_delta_min() -> None:
    summary = run_script()
    delta_min = 1.0 - math.exp(-4)

    assert math.isclose(summary["delta_min_numeric"], delta_min)
    assert summary["uniform_c_formula"] == "1/(1-delta_min)"
    assert math.isclose(summary["uniform_c_numeric"], 1.0 / (1.0 - delta_min))
    assert summary["uniform_m_formula"] == "delta_min/2"
    assert math.isclose(summary["uniform_m_numeric"], delta_min / 2.0)


def test_sprint94_remaining_open_lemmas_are_exact() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "WC3UniformInA",
        "UniformConnectedSchwingerDecay",
        "ContinuumLimitMassGap",
        "Nontrivial4DSU3YangMillsMeasure",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert summary["route_decision"] == "SPRINT94_CLOSES_UNIFORM_ACTIVITY_BOUND_ONLY"
