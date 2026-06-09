from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ym_sprint81d_effective_action_spatial_only_bridge_audit.py")


def run_audit(tmp_path: Path) -> Path:
    out_dir = tmp_path / "sprint81d"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    return out_dir


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_bridge_audit_writes_expected_artifacts(tmp_path: Path) -> None:
    out_dir = run_audit(tmp_path)

    assert (out_dir / "ym_sprint81d_spatial_only_bridge_table.csv").exists()
    assert (out_dir / "ym_sprint81d_gate_table.csv").exists()
    assert (out_dir / "ym_sprint81d_summary.json").exists()


def test_bridge_table_marks_evidence_open_and_assembly_defined(
    tmp_path: Path,
) -> None:
    out_dir = run_audit(tmp_path)
    rows = read_csv(out_dir / "ym_sprint81d_spatial_only_bridge_table.csv")

    evidence = next(
        row
        for row in rows
        if row["bridge_name"] == "ResidualEffectiveActionSpatialSupportEvidence"
    )
    assert evidence["status"] == "OPEN_ANALYTIC_INPUT"
    assert evidence["proved_in_repo"] == "False"

    assembly = next(
        row
        for row in rows
        if row["bridge_name"] == "effectiveActionPolymersSpatialOnlyForA1FromEvidence"
    )
    assert assembly["status"] == "DEFINED_CONDITIONAL_ASSEMBLY"
    assert assembly["proved_in_repo"] == "True"


def test_summary_keeps_kp_and_clay_fail_closed(tmp_path: Path) -> None:
    out_dir = run_audit(tmp_path)
    summary = json.loads((out_dir / "ym_sprint81d_summary.json").read_text())

    assert summary["support_interface_defined"] is True
    assert summary["spatial_only_bridge_defined"] is True
    assert summary["residual_effective_action_spatial_support_evidence"] is False
    assert (
        summary["effective_action_polymers_spatial_only_for_a1_conditional_assembly"]
        is True
    )
    assert summary["effective_action_polymers_spatial_only_for_a1_unconditional"] is False
    assert summary["kp_entropy_at_blocked_scale_l2"] is False
    assert summary["all_diameter_weighted_kp"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["next_required_gate"] == "ResidualEffectiveActionSpatialSupportEvidence"


def test_kp_arithmetic_guardrails_are_still_reported(tmp_path: Path) -> None:
    out_dir = run_audit(tmp_path)
    summary = json.loads((out_dir / "ym_sprint81d_summary.json").read_text())

    assert summary["eta4_kp_arithmetic_closes"] is True
    assert summary["eta4_q"] < 1
    assert summary["eta6_kp_arithmetic_fails"] is True
    assert summary["eta6_q"] > 1
    assert summary["eta8_kp_arithmetic_fails"] is True
    assert summary["eta8_q"] > 1
