from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint103_user_math_completion_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint103_user_math_completion"
    / "ym_sprint103_user_math_completion_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint103_records_user_math_for_all_eight_items() -> None:
    summary = run_script()

    assert summary["item_count"] == 8
    assert summary["user_supplied_math_for_all_eight"] is True
    assert summary["inhabited_receipts_for_all_eight"] is True
    assert all(item["user_supplied_math"] for item in summary["items"])
    assert all(item["inhabited_receipt_recorded"] for item in summary["items"])


def test_sprint103_keeps_clay_external_boundary_false() -> None:
    summary = run_script()
    names = {item["lemma"] for item in summary["items"]}

    assert "ContinuumLimitMassGap" in names
    assert "Nontrivial4DSU3YangMillsMeasure" in names
    assert summary["su3_k11_passes"] is True
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert (
        summary["route_decision"]
        == "SPRINT103_RECORDS_USER_MATH_FOR_ALL_EIGHT_NO_EXTERNAL_PROMOTION"
    )
