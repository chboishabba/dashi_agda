from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint95_kstar_collapse_source_matrix.py"
OUT_STEM = "ns_sprint95_kstar_collapse_source_matrix"

FORBIDDEN_DEPENDENCIES = (
    "clay",
    "target_absorption",
    "desired_conclusion",
    "bkm",
    "serrin",
    "h1_continuation",
    "theta_preservation",
    "option_c_conditional",
    "conditional_regular",
    "general_data_regular",
    "blowup_construction_assumed",
)

REQUIRED_GATES = (
    ("dominance",),
    ("pointwise", "h1", "tail"),
    ("independent", "coefficient"),
    ("same", "source"),
    ("finite", "time", "k", "collapse"),
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 95 K* collapse source matrix script is missing"

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
    assert md_paths, "audit did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    rows: list[dict[str, str]] = []
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


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def combined_payload(summary: dict[str, Any], rows: list[dict[str, str]]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": rows}


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint95_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "source matrix should expose at least one CSV row"
    assert re.search(r"sprint\s*95|sprint95", text, re.IGNORECASE)
    assert re.search(r"k\*|kstar|k-star|K\*", text)


def test_ns_sprint95_is_fail_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert summary.get("fail_closed") is True
    assert str(summary.get("route_decision", "")).upper() == "FAIL_CLOSED"
    assert str(summary.get("final_decision", "")).upper() == "FAIL_CLOSED"

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values)
    assert "FAIL_CLOSED" in text


def test_ns_sprint95_required_gates_are_reported(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    for terms in REQUIRED_GATES:
        assert values_for_key_terms(combined, *terms) or re.search(
            r"[\w *-]{0,80}".join(re.escape(term) for term in terms),
            combined_text,
            re.IGNORECASE,
        ), terms


def test_ns_sprint95_does_not_promote_clay(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values, "audit should expose Clay promotion state"
    assert not any(clay_values), clay_values
    assert re.search(r"clay", text, re.IGNORECASE)
    assert_no_true_assignment(text, "clay")


def test_ns_sprint95_forbidden_dependencies_are_reported_and_avoided(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    assert values_for_key_terms(combined, "forbidden"), "forbidden dependency policy missing"
    for dependency in FORBIDDEN_DEPENDENCIES:
        assert normalized(dependency) in normalized(combined_text), dependency

    forbidden_rows = [
        row
        for row in rows
        if re.search(r"forbidden|rejected|avoid", json.dumps(row), re.IGNORECASE)
    ]
    assert forbidden_rows, "matrix should include forbidden-dependency rejection evidence"
    assert not any(
        boolish(row.get("accepted")) is True or boolish(row.get("allowed")) is True
        for row in forbidden_rows
    )


def test_ns_sprint95_required_residual_is_finite_time_kstar_collapse_mechanism(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    residual_values = values_for_key_terms(combined, "required", "residual")
    assert residual_values, "summary should expose the required residual"
    residual_text = "\n".join(str(value) for value in residual_values) + "\n" + text

    assert re.search(r"finite[- ]time", residual_text, re.IGNORECASE)
    assert re.search(r"k\*|kstar|k-star|K\*", residual_text)
    assert re.search(r"collapse", residual_text, re.IGNORECASE)
    assert re.search(r"mechanism", residual_text, re.IGNORECASE)
