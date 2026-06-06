from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint102_proof_obligation_index_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint102_proof_obligation_index"
    / "ym_sprint102_proof_obligation_index_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint102_indexes_eight_remaining_analytic_obligations() -> None:
    summary = run_script()

    assert summary["receipt_layer_present"] is True
    assert summary["analytic_proof_layer_complete"] is False
    assert summary["remaining_analytic_obligation_count"] == 8
    assert all(
        item["receipt_or_interface_in_repo"] is True
        for item in summary["remaining_analytic_obligations"]
    )
    assert all(
        item["analytic_proof_in_repo"] is False
        for item in summary["remaining_analytic_obligations"]
    )


def test_sprint102_keeps_external_and_clay_boundaries_fail_closed() -> None:
    summary = run_script()
    names = {item["lemma"] for item in summary["remaining_analytic_obligations"]}

    assert "ContinuumLimitMassGap" in names
    assert "Nontrivial4DSU3YangMillsMeasure" in names
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert (
        summary["route_decision"]
        == "SPRINT102_INDEXES_RECEIPTS_VS_REAL_PROOFS_NO_PROMOTION"
    )
