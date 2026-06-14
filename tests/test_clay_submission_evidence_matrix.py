from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "clay_submission_evidence_matrix.py"
EXPECTED_DOMAINS = ["NS", "YM", "Paper8/UCT"]
EXPECTED_REQUIRED = [
    "scripts/ns_missing_math_theorem_agenda.py",
    "scripts/ym_missing_math_theorem_agenda.py",
    "scripts/uct_missing_math_theorem_agenda.py",
]
EXPECTED_OPTIONAL_AUDITS = {
    "scripts/ns_stationarity_candidate_audit.py",
    "scripts/ns_kappa_bias_candidate_audit.py",
    "scripts/ns_sprint93_candidate_source_matrix_audit.py",
    "scripts/ym_finite_domination_candidate_audit.py",
    "scripts/ym_sprint98_clay_statement_boundary_candidate_audit.py",
    "scripts/ym_sprint112_map_candidate_reduction_audit.py",
}


def run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--repo-root", str(REPO_ROOT), *args],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def load_payload() -> dict[str, Any]:
    result = run_script()
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert isinstance(payload, dict)
    return payload


def test_matrix_emits_required_domains_and_fields() -> None:
    payload = load_payload()

    assert payload["schema"] == "dashi.clay_submission_evidence_matrix.v1"
    assert payload["ok"] is True
    assert payload["fail_closed"] is True
    assert payload["domains"] == EXPECTED_DOMAINS
    assert payload["required_agenda_scripts"] == EXPECTED_REQUIRED

    rows = payload["matrix"]
    assert [row["domain"] for row in rows] == EXPECTED_DOMAINS
    for row in rows:
        for key in (
            "submission_ready_as_reduction",
            "clay_eligible_proof",
            "authority_backed",
            "internal_proof_required",
            "first_blocker",
            "needed_user_math",
        ):
            assert key in row, row
        assert isinstance(row["first_blocker"], str) and row["first_blocker"]
        assert isinstance(row["needed_user_math"], list) and row["needed_user_math"]
        assert row["agenda_ok"] is True


def test_matrix_is_fail_closed_for_all_current_clay_domains() -> None:
    payload = load_payload()

    assert payload["clay_eligible_domains"] == []
    for row in payload["matrix"]:
        assert row["clay_eligible_proof"] is False
        assert row["submission_ready_as_reduction"] is False
        assert row["internal_proof_required"] is True
        assert row["all_blockers_proved"] is False
        assert row["blocker_count"] > 0


def test_authority_backing_is_reflected_but_not_promoted() -> None:
    rows = {row["domain"]: row for row in load_payload()["matrix"]}

    assert rows["NS"]["authority_backed"] is False
    assert rows["YM"]["authority_backed"] is True
    assert rows["Paper8/UCT"]["authority_backed"] is True
    assert rows["YM"]["clay_eligible_proof"] is False
    assert rows["Paper8/UCT"]["clay_eligible_proof"] is False


def test_optional_candidate_audit_surfaces_are_named_and_reflected_if_present() -> None:
    payload = load_payload()

    assert set(payload["optional_candidate_audit_scripts"]) == EXPECTED_OPTIONAL_AUDITS
    audits = [
        audit
        for row in payload["matrix"]
        for audit in row["candidate_audits"]
    ]
    assert {audit["script"] for audit in audits} == EXPECTED_OPTIONAL_AUDITS
    for audit in audits:
        assert audit["script_present"] is True
        assert audit["clay_promotion_detected"] is False
        assert audit["reflection_status"] == "present"


def test_markdown_contains_required_matrix_columns() -> None:
    result = run_script("--format", "md")
    assert result.returncode == 0, result.stdout + result.stderr

    assert "# Clay Submission Evidence Matrix" in result.stdout
    assert "submission_ready_as_reduction" in result.stdout
    assert "clay_eligible_proof" in result.stdout
    for domain in EXPECTED_DOMAINS:
        assert domain in result.stdout
