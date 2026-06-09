from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint95_uniform_connected_schwinger_decay_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint95_uniform_connected_schwinger_decay"
    / "ym_sprint95_uniform_connected_schwinger_decay_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint95_closes_uniform_connected_schwinger_decay_only() -> None:
    summary = run_script()

    assert summary["wc3_uniform_in_a_required"] is True
    assert summary["connected_mayer_expansion_used"] is True
    assert summary["uniform_connected_schwinger_decay_closed_in_repo"] is True
    assert summary["continuum_limit_mass_gap_derived_in_repo"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint95_schwinger_decay_statement_is_uniform_in_a() -> None:
    summary = run_script()

    assert "uniformly for a < a0" in summary["decay_statement"]
    assert "exp(-m * tree_dist" in summary["decay_statement"]


def test_sprint95_schwinger_remaining_open_lemmas_are_exact() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "ContinuumLimitMassGap",
        "Nontrivial4DSU3YangMillsMeasure",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert (
        summary["route_decision"]
        == "SPRINT95_CLOSES_UNIFORM_CONNECTED_SCHWINGER_DECAY_ONLY"
    )
