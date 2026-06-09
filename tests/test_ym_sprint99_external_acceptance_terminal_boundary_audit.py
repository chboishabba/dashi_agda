from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint99_external_acceptance_terminal_boundary_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint99_external_acceptance_terminal_boundary"
    / "ym_sprint99_external_acceptance_terminal_boundary_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint99_records_terminal_fail_closed_boundary() -> None:
    summary = run_script()

    assert summary["sprint98_clay_statement_boundary_required"] is True
    assert summary["internal_candidate_chain_complete_in_repo"] is True
    assert summary["external_acceptance_token_available"] is False
    assert summary["external_acceptance_token_repo_internal"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint99_terminal_boundary_statement_is_governance_not_math() -> None:
    summary = run_script()

    assert "governance/review artifact" in summary["terminal_boundary_statement"]
    assert "not an Agda proof object" in summary["terminal_boundary_statement"]


def test_sprint99_remaining_items_are_external() -> None:
    summary = run_script()

    assert summary["remaining_external_items"] == [
        "external peer review",
        "community acceptance",
        "Clay acceptance",
    ]
    assert (
        summary["route_decision"]
        == "SPRINT99_TERMINAL_FAIL_CLOSED_EXTERNAL_ACCEPTANCE_BOUNDARY"
    )
