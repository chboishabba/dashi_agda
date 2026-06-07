from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


SCRIPT = Path("scripts/ns_sprint88_h1_tail_smallness_decision_audit.py")
OUT_NAME = "ns_sprint88_h1_tail_smallness_decision"


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any]]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 88 H1-tail smallness decision audit script is not present.")

    out_dir = tmp_path / OUT_NAME
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )

    summary_path = out_dir / f"{OUT_NAME}_summary.json"
    assert summary_path.exists()
    return out_dir, json.loads(summary_path.read_text())


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def bool_value(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value == "True"
    return False


def first_present(summary: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        if key in summary:
            return summary[key]
    raise AssertionError(f"missing expected summary key alias: {', '.join(keys)}")


def test_ns_sprint88_outputs_and_required_anchors(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint88_h1_tail_smallness_decision_audit"
    assert (out_dir / f"{OUT_NAME}_summary.json").exists()
    assert (out_dir / f"{OUT_NAME}_report.md").exists()
    assert (out_dir / f"{OUT_NAME}_gate_table.csv").exists()

    assert first_present(
        summary,
        (
            "all_required_receipt_anchors_present",
            "required_receipt_anchors_present",
        ),
    ) is True

    source_rows = read_csv(out_dir / f"{OUT_NAME}_source_table.csv")
    receipt_rows = [
        row
        for row in source_rows
        if row["surface_name"] == "Sprint88H1TailSmallnessDecisionReceipt"
    ]
    assert receipt_rows
    assert receipt_rows[0]["present_in_repo"] == "True"
    assert receipt_rows[0]["missing_anchors"] == "none"


def test_ns_sprint88_decision_flags_fail_closed(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / f"{OUT_NAME}_gate_table.csv")
    gates_by_name = {row["gate_name"]: row for row in gate_rows}

    assert first_present(
        summary,
        (
            "sprint87_danger_shell_factorization_inherited",
            "inherited_sprint87_factorization",
            "sprint87_factorization_inherited",
            "sprint87_factorization_inherited_closed",
        ),
    ) is True
    assert first_present(
        summary,
        (
            "kstar_admissibility_insufficient_for_h1_tail_smallness",
            "kstar_insufficiency_recorded",
            "kstar_insufficient",
            "kstar_admissibility_alone_insufficient",
        ),
    ) is True
    assert first_present(
        summary,
        (
            "leray_energy_insufficient_for_h1_tail_smallness",
            "leray_insufficiency_recorded",
            "leray_insufficient",
            "leray_energy_alone_insufficient",
        ),
    ) is True
    assert first_present(
        summary,
        (
            "time_integrated_tail_control_insufficient_for_pointwise_h1_tail",
            "time_integrated_insufficiency_recorded",
            "time_integrated_insufficient",
            "time_integrated_dissipation_pointwise_insufficient",
        ),
    ) is True
    assert first_present(
        summary,
        (
            "h1_tail_smallness_closure_proved_in_repo",
            "h1_tail_smallness_closure_closed",
            "h1_tail_closure",
            "non_circular_danger_shell_h1_tail_smallness_closed",
        ),
    ) is False
    assert first_present(
        summary,
        (
            "absorption_proved_in_repo",
            "absorption_closed",
            "unconditional_absorption_closed",
            "danger_shell_absorption_condition_closed",
        ),
    ) is False
    assert first_present(
        summary,
        (
            "clay_navier_stokes_promoted",
            "clay_ns_promoted",
            "clay_promotion",
        ),
    ) is False

    for gate_name in {
        "Sprint87FactorizationInheritedClosed",
        "KStarAdmissibilityAloneInsufficient",
        "LerayEnergyAloneInsufficient",
        "TimeIntegratedDissipationPointwiseInsufficient",
        "NonCircularDangerShellH1TailSmallnessClosed",
        "DangerShellAbsorptionConditionClosed",
        "ClayNavierStokesPromoted",
    }:
        assert gate_name in gates_by_name

    assert bool_value(
        gates_by_name["Sprint87FactorizationInheritedClosed"]["actual_value"]
    )
    assert bool_value(
        gates_by_name["KStarAdmissibilityAloneInsufficient"]["actual_value"]
    )
    assert bool_value(gates_by_name["LerayEnergyAloneInsufficient"]["actual_value"])
    assert bool_value(
        gates_by_name["TimeIntegratedDissipationPointwiseInsufficient"][
            "actual_value"
        ]
    )
    assert not bool_value(
        gates_by_name["NonCircularDangerShellH1TailSmallnessClosed"]["actual_value"]
    )
    assert not bool_value(
        gates_by_name["DangerShellAbsorptionConditionClosed"]["actual_value"]
    )
    assert gates_by_name["ClayNavierStokesPromoted"]["clay_promotion"] == "False"
    assert all(row.get("clay_promotion", "False") == "False" for row in gate_rows)
