from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


SCRIPT = Path("scripts/ns_sprint87_danger_shell_factorization_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any]]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 87 danger-shell factorization audit script is not present.")

    out_dir = tmp_path / "ns_sprint87_danger_shell_factorization"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )

    summary_paths = sorted(out_dir.glob("*summary.json"))
    assert summary_paths == [
        out_dir / "ns_sprint87_danger_shell_factorization_summary.json"
    ]
    return out_dir, json.loads(summary_paths[0].read_text())


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
    missing = ", ".join(keys)
    raise AssertionError(f"missing expected summary key alias: {missing}")


def test_ns_sprint87_outputs_json_and_markdown(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint87_danger_shell_factorization_audit"
    assert (out_dir / "ns_sprint87_danger_shell_factorization_summary.json").exists()
    assert (out_dir / "ns_sprint87_danger_shell_factorization_report.md").exists()
    assert (out_dir / "ns_sprint87_danger_shell_factorization_gate_table.csv").exists()


def test_ns_sprint87_required_receipt_anchors_present(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert first_present(
        summary,
        (
            "all_required_receipt_anchors_present",
            "required_receipt_anchors_present",
        ),
    ) is True

    anchor_tables = [
        path
        for path in out_dir.glob("*.csv")
        if "anchor" in path.name or "receipt" in path.name or "surface" in path.name
    ]
    assert anchor_tables, "expected a receipt-anchor CSV table"

    rows = [row for table in anchor_tables for row in read_csv(table)]
    anchor_rows = [row for row in rows if row.get("required_anchor")]
    assert anchor_rows, "expected required_anchor rows"
    assert all(bool_value(row.get("present_in_receipt")) for row in anchor_rows)


def test_ns_sprint87_factorization_gates_closed_without_absorption(
    tmp_path: Path,
) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint87_danger_shell_factorization_gate_table.csv")

    closed_factorization_gates = [
        row
        for row in gate_rows
        if "Factorization" in row.get("gate_name", "")
        and bool_value(row.get("actual_value"))
    ]

    assert len(closed_factorization_gates) == 3
    assert all("CLOSED" in row.get("status", "") for row in closed_factorization_gates)
    assert first_present(
        summary,
        (
            "danger_shell_absorption_proved_in_repo",
            "danger_shell_absorption_closed",
            "absorption_proved_in_repo",
            "absorption_closed",
        ),
    ) is False


def test_ns_sprint87_keeps_clay_ns_promotion_false(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint87_danger_shell_factorization_gate_table.csv")

    assert first_present(
        summary,
        (
            "clay_navier_stokes_promoted",
            "clay_ns_promoted",
        ),
    ) is False
    assert first_present(
        summary,
        (
            "clay_promotion_recorded_false",
            "clay_navier_stokes_promotion_recorded_false",
            "clay_ns_promotion_recorded_false",
        ),
    ) is True

    clay_rows = [
        row
        for row in gate_rows
        if row.get("gate_name") in {"ClayNavierStokesPromoted", "ClayNSPromoted"}
    ]
    assert clay_rows
    assert all(row.get("clay_promotion") == "False" for row in clay_rows)
