from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint100_terminal_state_rollup_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint100_terminal_state_rollup"
    / "ym_sprint100_terminal_state_rollup_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint100_rollup_preserves_terminal_state() -> None:
    summary = run_script()

    assert summary["imports_sprints"] == list(range(91, 101))
    assert summary["internal_candidate_chain_complete_in_repo"] is True
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint100_rollup_records_all_internal_layers() -> None:
    summary = run_script()

    assert summary["wc3_route_recorded"] is True
    assert summary["wc3_uniform_in_a_closed_in_receipt_layer"] is True
    assert summary["uniform_connected_schwinger_decay_closed_in_receipt_layer"] is True
    assert summary["continuum_limit_mass_gap_closed_in_receipt_layer"] is True
    assert summary["nontrivial_su3_measure_closed_in_receipt_layer"] is True
    assert summary["clay_statement_boundary_closed_in_receipt_layer"] is True


def test_sprint100_rollup_is_not_promotion() -> None:
    summary = run_script()

    assert "clayYangMillsPromoted=false" in summary["terminal_state_statement"]
    assert summary["remaining_external_items"] == [
        "external peer review",
        "community acceptance",
        "Clay acceptance",
    ]
    assert summary["route_decision"] == "SPRINT100_ROLLUP_ONLY_NO_PROMOTION"
