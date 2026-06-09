from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint101_clay_boundary_reconciliation_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint101_clay_boundary_reconciliation"
    / "ym_sprint101_clay_boundary_reconciliation_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint101_reconciles_new_and_legacy_boundaries() -> None:
    summary = run_script()

    assert summary["sprint100_internal_candidate_chain_complete"] is True
    assert summary["sprint100_external_acceptance_available"] is False
    assert summary["legacy_all_providers_derived_in_repo"] is False
    assert summary["legacy_clay_statement_boundary_discharged"] is False


def test_sprint101_both_boundaries_remain_non_promoting() -> None:
    summary = run_script()

    assert summary["legacy_clay_yang_mills_promoted"] is False
    assert summary["sprint100_clay_yang_mills_promoted"] is False
    assert "clayYangMillsPromoted=false" in summary["reconciliation_statement"]
    assert summary["route_decision"] == "SPRINT101_RECONCILES_BOUNDARIES_NO_PROMOTION"
