from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint98_clay_statement_boundary_candidate_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint98_clay_statement_boundary_candidate"
    / "ym_sprint98_clay_statement_boundary_candidate_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint98_closes_internal_boundary_only() -> None:
    summary = run_script()

    assert summary["sprint97_nontrivial_su3_measure_required"] is True
    assert summary["continuum_existence_surface_recorded"] is True
    assert summary["positive_continuum_mass_gap_surface_recorded"] is True
    assert summary["clay_statement_formulation_match_recorded"] is True
    assert summary["clay_statement_boundary_discharged_in_repo"] is True
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint98_boundary_statement_preserves_external_boundary() -> None:
    summary = run_script()

    assert "Internal Clay statement boundary discharged" in summary["boundary_statement"]
    assert "external acceptance remains unavailable" in summary["boundary_statement"]


def test_sprint98_remaining_open_lemmas_are_exact() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "ExternalAcceptanceToken",
    ]
    assert (
        summary["route_decision"]
        == "SPRINT98_CLOSES_INTERNAL_CLAY_STATEMENT_BOUNDARY_ONLY"
    )
