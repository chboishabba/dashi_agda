from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


SCRIPT = Path("scripts/ns_sprint89_pointwise_h1_tail_mechanism_audit.py")
OUT_NAME = "ns_sprint89_pointwise_h1_tail_mechanism_audit"

REQUIRED_ANCHORS = {
    "canonicalNSSprint89PointwiseH1TailMechanismReceipt",
    "sprint88H1TailDecisionInheritedClosed",
    "pointwiseH1TailMechanismClosed",
    "dangerShellTailSmallnessClosed",
    "dangerShellAbsorptionConditionClosed",
    "clayNavierStokesPromoted",
}

CLOSED_FLAG_ALIASES = {
    "sprint88_h1_tail_decision_inherited_closed": (
        "sprint88_h1_tail_decision_inherited_closed",
        "sprint88_decision_inherited_closed",
        "sprint88_h1_tail_smallness_decision_inherited_closed",
    ),
    "pointwise_h1_tail_mechanism_closed": (
        "pointwise_h1_tail_mechanism_closed",
        "pointwise_h1_tail_closed",
        "non_circular_pointwise_h1_tail_mechanism_closed",
    ),
    "danger_shell_tail_smallness_closed": (
        "danger_shell_tail_smallness_closed",
        "danger_shell_h1_tail_smallness_closed",
        "h1_tail_smallness_closure_closed",
    ),
    "danger_shell_absorption_condition_closed": (
        "danger_shell_absorption_condition_closed",
        "absorption_closed",
        "unconditional_absorption_closed",
    ),
}

PROMOTION_ALIASES = (
    "clay_navier_stokes_promoted",
    "clay_ns_promoted",
    "clay_promotion",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any]]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 89 pointwise H1-tail mechanism audit script is not present.")

    out_dir = tmp_path / OUT_NAME
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )

    summaries = sorted(out_dir.glob("*.json"))
    assert summaries, "audit did not write a JSON summary"
    summary_path = next(
        (
            path
            for path in summaries
            if path.name.endswith("_summary.json") or "summary" in path.name
        ),
        summaries[0],
    )
    return out_dir, json.loads(summary_path.read_text())


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def bool_value(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.lower() == "true"
    return False


def first_present(summary: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        if key in summary:
            return summary[key]
    raise AssertionError(f"missing expected summary key alias: {', '.join(keys)}")


def normalized_route(summary: dict[str, Any]) -> str:
    route = str(summary.get("route_decision", ""))
    return route.replace("_", "-").lower()


def csv_rows(out_dir: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in sorted(out_dir.glob("*.csv")):
        rows.extend(read_csv(path))
    return rows


def test_ns_sprint89_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint89_pointwise_h1_tail_mechanism_audit"
    assert list(out_dir.glob("*.json")), "expected JSON output"
    assert list(out_dir.glob("*.csv")), "expected CSV output"
    assert list(out_dir.glob("*.md")), "expected Markdown output"


def test_ns_sprint89_required_anchors_are_present(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert first_present(
        summary,
        (
            "all_required_receipt_anchors_present",
            "required_receipt_anchors_present",
        ),
    ) is True

    rows = csv_rows(out_dir)
    anchor_text = "\n".join(
        " ".join(str(value) for value in row.values()) for row in rows
    )
    for anchor in REQUIRED_ANCHORS:
        assert anchor in anchor_text or anchor in json.dumps(summary)

    missing_anchor_rows = [
        row
        for row in rows
        if row.get("missing_anchors") not in {None, "", "none"}
        or row.get("present_in_receipt") == "False"
    ]
    assert not missing_anchor_rows


def test_ns_sprint89_closed_flags_and_promotion_boundary(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    rows = csv_rows(out_dir)
    gates_by_name = {row.get("gate_name", ""): row for row in rows}

    assert first_present(
        summary,
        CLOSED_FLAG_ALIASES["sprint88_h1_tail_decision_inherited_closed"],
    ) is True
    for key in (
        "pointwise_h1_tail_mechanism_closed",
        "danger_shell_tail_smallness_closed",
        "danger_shell_absorption_condition_closed",
    ):
        assert first_present(summary, CLOSED_FLAG_ALIASES[key]) is False

    assert first_present(summary, PROMOTION_ALIASES) is False
    assert all(row.get("clay_promotion", "False") == "False" for row in rows)

    for gate_name in {
        "Sprint88H1TailDecisionInheritedClosed",
    }:
        if gate_name in gates_by_name:
            assert bool_value(gates_by_name[gate_name].get("actual_value"))
    for gate_name in {
        "PointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        "LocalEnstrophyDangerShellDissipationClosed",
        "TimeIntegratedToPointwiseConversionClosed",
        "IndependentEpsilonCoefficientClosed",
    }:
        if gate_name in gates_by_name:
            assert not bool_value(gates_by_name[gate_name].get("actual_value"))

    clay_rows = [
        row
        for row in rows
        if row.get("gate_name") in {"ClayNavierStokesPromoted", "ClayNSPromoted"}
    ]
    assert clay_rows
    assert all(row.get("clay_promotion") == "False" for row in clay_rows)


def test_ns_sprint89_route_decision_is_fail_closed(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    report_text = "\n".join(path.read_text() for path in sorted(out_dir.glob("*.md")))

    assert normalized_route(summary) == "fail-closed"
    assert bool_value(summary.get("fail_closed", True)) is True
    assert "fail" in report_text.lower()
    assert "closed" in report_text.lower()
