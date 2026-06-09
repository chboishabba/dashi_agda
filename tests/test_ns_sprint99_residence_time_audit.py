from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint99_residence_time_audit.py"
OUT_STEM = "ns_sprint99_residence_time_audit"
ROUTE_DECISION = "FAIL_CLOSED_RESIDENCE_TIME_AGAINST_VISCOSITY"

REQUIRED_MISSING_OBJECTS = (
    "LowModeResidenceWindow",
    "ViscousDampingDefeatEstimate",
    "PersistentLowModeEnergyReservoir",
    "TimeIntegratedFluxSurplus",
    "LerayCompatibleResidenceTrajectory",
)

FORBIDDEN_MARKERS = (
    "postulate",
    "TODO",
    "stub",
    "skeleton",
    "admit",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint99 residence-time audit script is missing"

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
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    rows: list[dict[str, Any]] = []
    if isinstance(summary.get("rows"), list):
        rows.extend(row for row in summary["rows"] if isinstance(row, dict))

    for path in json_paths:
        if path == summary_path:
            continue
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, list):
            rows.extend(row for row in payload if isinstance(row, dict))
        elif isinstance(payload, dict) and isinstance(payload.get("rows"), list):
            rows.extend(row for row in payload["rows"] if isinstance(row, dict))
        elif isinstance(payload, dict):
            for key, value in payload.items():
                if isinstance(value, list):
                    rows.extend(
                        {"_json_name": path.name, "_row_group": key, **row}
                        for row in value
                        if isinstance(row, dict)
                    )

    csv_paths = sorted(out_dir.glob("*.csv"))
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    for path in [*json_paths, *csv_paths, *md_paths]:
        parts.append(path.read_text(encoding="utf-8"))
    return out_dir, summary, rows, "\n".join(parts)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def normalized(value: object) -> str:
    return str(value).strip().replace("_", "-").lower()


def boolish(value: object) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        if value == 1:
            return True
        if value == 0:
            return False
    if isinstance(value, str):
        lowered = normalized(value)
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "accepted", "promoted"}:
            return True
        if lowered in {
            "false",
            "0",
            "no",
            "fail",
            "failed",
            "open",
            "blocked",
            "rejected",
            "not-promoted",
            "fail-closed",
            "hold",
        }:
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


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def combined_payload(summary: dict[str, Any], rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {"summary": summary, "rows": rows}


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint99_audit_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "residence-time audit should expose evidence rows"
    assert re.search(r"sprint\s*99|sprint99", text, re.IGNORECASE)
    assert re.search(r"residence[-_ ]?time", text, re.IGNORECASE)


def test_ns_sprint99_summary_booleans_fail_closed_without_completion(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["fail_closed"] is True
    assert summary["complete"] is False
    assert summary["residence_time_against_viscosity_closed"] is False
    assert summary["finite_time_kstar_collapse_closed"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert summary["route_decision"] == ROUTE_DECISION
    assert summary["final_decision"] == ROUTE_DECISION

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values), fail_closed_values
    assert ROUTE_DECISION in text


def test_ns_sprint99_lists_exact_required_missing_objects(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    assert summary["missing_analytic_objects"] == list(REQUIRED_MISSING_OBJECTS)
    assert summary["missing_analytic_object_count"] == len(REQUIRED_MISSING_OBJECTS)
    for missing_object in REQUIRED_MISSING_OBJECTS:
        assert normalized(missing_object) in normalized(combined_text), missing_object


def test_ns_sprint99_has_no_forbidden_markers(tmp_path: Path) -> None:
    _out_dir, summary, rows, _text = run_audit(tmp_path)

    assert summary["forbidden_marker_count"] == 0
    assert summary["forbidden_hits"] == []
    forbidden_values = bool_values_for_key_terms(combined_payload(summary, rows), "forbidden")
    assert forbidden_values and not any(forbidden_values), forbidden_values
    for marker in FORBIDDEN_MARKERS:
        assert marker in summary["forbidden_markers"], marker


def test_ns_sprint99_route_and_final_decision_fail_closed_with_clay_false(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary.get("route_decision") == ROUTE_DECISION
    assert summary.get("final_decision") == ROUTE_DECISION
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values and not any(clay_values), clay_values
    assert_no_true_assignment(text, "clay")
    assert_no_true_assignment(text, "complete")
