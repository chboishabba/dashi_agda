from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint97_nontrivial_su3_continuum_measure_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint97_nontrivial_su3_continuum_measure"
    / "ym_sprint97_nontrivial_su3_continuum_measure_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint97_closes_nontrivial_su3_measure_only() -> None:
    summary = run_script()

    assert summary["continuum_limit_mass_gap_required"] is True
    assert summary["su3_nonabelian_curvature_self_interaction_recorded"] is True
    assert summary["non_gaussian_connected_correlation_witness_recorded"] is True
    assert (
        summary["nontrivial_4d_su3_yang_mills_measure_closed_in_repo"] is True
    )
    assert summary["clay_statement_boundary_discharged"] is False
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint97_nontriviality_statement_mentions_non_gaussianity() -> None:
    summary = run_script()

    assert "nontrivial/non-Gaussian" in summary["nontriviality_statement"]
    assert "non-Abelian curvature self-interaction" in summary["nontriviality_statement"]
    assert "higher connected correlations" in summary["nontriviality_statement"]


def test_sprint97_remaining_open_lemmas_are_exact() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert (
        summary["route_decision"]
        == "SPRINT97_CLOSES_NONTRIVIAL_SU3_MEASURE_ONLY"
    )
