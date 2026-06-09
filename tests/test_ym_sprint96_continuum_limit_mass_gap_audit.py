from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint96_continuum_limit_mass_gap_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint96_continuum_limit_mass_gap"
    / "ym_sprint96_continuum_limit_mass_gap_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint96_closes_continuum_limit_mass_gap_only() -> None:
    summary = run_script()

    assert summary["uniform_connected_schwinger_decay_required"] is True
    assert summary["rg_generated_mass_term_scoped_authority"] is True
    assert summary["transfer_gap_tracks_effective_mass_recorded"] is True
    assert summary["rg_invariant_physical_scale_recorded"] is True
    assert summary["continuum_limit_mass_gap_closed_in_repo"] is True
    assert (
        summary["nontrivial_4d_su3_yang_mills_measure_derived_in_repo"]
        is False
    )
    assert summary["clay_statement_boundary_discharged"] is False
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint96_mass_gap_statement_uses_rg_scaled_gap() -> None:
    summary = run_script()

    assert "lim_{a->0}" in summary["continuum_mass_gap_statement"]
    assert "gap(T(a))*block_size(a)" in summary["continuum_mass_gap_statement"]
    assert "m_phys > 0" in summary["continuum_mass_gap_statement"]


def test_sprint96_remaining_open_lemmas_are_exact() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "Nontrivial4DSU3YangMillsMeasure",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert (
        summary["route_decision"]
        == "SPRINT96_CLOSES_CONTINUUM_LIMIT_MASS_GAP_ONLY"
    )
