from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint94_kstar_fork_obstruction_audit.py"
OUT_STEM = "ns_sprint94_kstar_fork_obstruction_audit"

REQUIRED_ANCHORS = (
    "NSSprint94",
    "Sprint94",
    "KStarForkObstruction",
    "conditional",
    "general-data",
    "blowup",
    "Clay",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 94 KStar fork obstruction audit script is missing"

    out_dir = tmp_path / OUT_STEM
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode in (0, 1), result.stdout + result.stderr

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "audit did not write JSON output"
    assert csv_paths, "audit did not write CSV output"
    assert md_paths, "audit did not write Markdown report"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    rows: list[dict[str, str]] = []
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))

    text_parts = [json.dumps(summary, sort_keys=True)]
    text_parts.extend(path.read_text(encoding="utf-8") for path in [*json_paths, *csv_paths, *md_paths])
    return out_dir, summary, rows, "\n".join(text_parts)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"true", "1", "yes", "closed", "pass", "passed", "promoted", "accepted"}:
            return True
        if lowered in {"false", "0", "no", "open", "fail", "failed", "rejected", "not_promoted"}:
            return False
    return None


def values_for_key_terms(payload: Any, *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if all(pattern.search(str(key)) for pattern in patterns):
                values.append(value)
    return values


def payload(summary: dict[str, Any], rows: list[dict[str, str]]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": rows}


def assert_bool_field(
    combined: dict[str, Any],
    text: str,
    expected: bool,
    *terms: str,
) -> None:
    values = values_for_key_terms(combined, *terms)
    bool_values = [parsed for parsed in (boolish(value) for value in values) if parsed is not None]
    assert bool_values, f"missing bool evidence for {'/'.join(terms)}"
    assert expected in bool_values, f"{'/'.join(terms)} never recorded as {expected}"

    unexpected = "false" if expected else "true"
    assignment = re.compile(
        r"[\w -]*".join(re.escape(term) for term in terms)
        + rf"[\w -]{{0,100}}[:=]\s*{unexpected}\b",
        re.IGNORECASE,
    )
    assert not assignment.search(text), f"{'/'.join(terms)} unexpectedly recorded as {unexpected}"


def test_ns_sprint94_writes_required_outputs_and_required_fields(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary["contract"] == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "audit CSV outputs should expose rows"

    for key in (
        "contract",
        "complete",
        "route_decision",
        "final_decision",
        "fail_closed",
        "clay_navier_stokes_promoted",
        "conditional_criterion_closed",
        "general_data_gate_closed",
        "blowup_construction_closed",
    ):
        assert key in summary, key

    assert "fail_closed" in text.lower()


def test_ns_sprint94_required_anchors_exist_in_reported_output(tmp_path: Path) -> None:
    _out_dir, _summary, _rows, text = run_audit(tmp_path)

    for anchor in REQUIRED_ANCHORS:
        assert re.search(re.escape(anchor), text, re.IGNORECASE), anchor


def test_ns_sprint94_audit_passes_fail_closed(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    assert summary["complete"] is False
    assert summary["fail_closed"] is True
    assert "FAIL_CLOSED" in {str(summary["route_decision"]), str(summary["final_decision"])}
    assert_bool_field(combined, text, True, "fail", "closed")


def test_ns_sprint94_clay_and_general_data_paths_remain_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["general_data_gate_closed"] is False
    assert_bool_field(combined, text, False, "clay")
    assert_bool_field(combined, text, False, "general", "data")


def test_ns_sprint94_conditional_closed_true_and_blowup_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    assert summary["conditional_criterion_closed"] is True
    assert summary["blowup_construction_closed"] is False
    assert_bool_field(combined, text, True, "conditional", "closed")
    assert_bool_field(combined, text, False, "blowup")
