from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint103_nontrivial_su3_obligation8_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint103_nontrivial_su3_obligation8"
    / "ym_sprint103_nontrivial_su3_obligation8_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint103_obligation8_closes_nontrivial_su3_measure_only() -> None:
    summary = run_script()

    assert summary["worker"] == "D"
    assert summary["obligation_number"] == 8
    assert summary["uses_sprint97_context"] is True
    assert summary["continuum_measure_obligation8_closed_in_repo"] is True
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["clay_statement_boundary_discharged"] is False
    assert summary["external_acceptance_token_available"] is False
    assert (
        summary["route_decision"]
        == "SPRINT103_OBLIGATION8_CLOSES_NONTRIVIAL_SU3_MEASURE_ONLY"
    )


def test_sprint103_obligation8_has_stronger_interaction_witnesses() -> None:
    summary = run_script()

    assert summary["explicit_nonabelian_curvature_recorded"] is True
    assert summary["cubic_self_interaction_recorded"] is True
    assert summary["quartic_self_interaction_recorded"] is True
    assert (
        summary["non_gaussian_connected_correlation_witness_recorded"] is True
    )
    assert summary["required_term_checks"]["F_mu_nu^a"] is True
    assert summary["required_term_checks"]["g f^{abc} A_mu^b A_nu^c"] is True
    assert summary["required_term_checks"]["kappa_4"] is True


def test_sprint103_obligation8_has_no_empty_skeletons_or_postulates() -> None:
    summary = run_script()

    assert summary["audit_passed"] is True
    assert summary["no_empty_data_skeletons"] is True
    assert summary["no_postulates"] is True
