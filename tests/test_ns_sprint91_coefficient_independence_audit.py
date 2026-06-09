from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint91_coefficient_independence_audit.py"
OUT_STEM = "ns_sprint91_coefficient_independence_audit"
REQUIRED_RESIDUAL_GATE = "PointwiseH1TailWithIndependentEpsilonCoefficient"


EXPECTED_CANDIDATE_TERMS = (
    "fixed-K LP identity",
    "adjacent leakage",
    "local-enstrophy",
    "scalar epsilon solver",
    "target absorption",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 91 coefficient independence audit script is missing"

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

    summary_path = next(
        (path for path in json_paths if "summary" in path.name),
        json_paths[0],
    )
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    rows: list[dict[str, str]] = []
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))

    text_parts = [json.dumps(summary, sort_keys=True)]
    for path in [*json_paths, *csv_paths, *md_paths]:
        text_parts.append(path.read_text(encoding="utf-8"))
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
        if lowered in {"true", "1", "yes", "closed", "pass", "allowed"}:
            return True
        if lowered in {"false", "0", "no", "open", "fail", "rejected"}:
            return False
    return None


def row_text(row: dict[str, str]) -> str:
    return json.dumps(row, sort_keys=True)


def values_matching_keys(summary: dict[str, Any], *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if all(pattern.search(str(key)) for pattern in patterns):
                values.append(value)
    return values


def summary_value(summary: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in summary:
            return summary[key]
    nested = [
        value
        for item in flatten(summary)
        if isinstance(item, dict)
        for key, value in item.items()
        if key in keys
    ]
    assert nested, f"missing summary key alias: {', '.join(keys)}"
    return nested[0]


def normalized(value: object) -> str:
    return str(value).strip().replace("_", "-").lower()


def test_ns_sprint91_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert "sprint91" in text.lower() or "Sprint 91" in text


def test_ns_sprint91_candidate_rows_cover_required_sources(tmp_path: Path) -> None:
    _out_dir, _summary, rows, text = run_audit(tmp_path)

    candidate_rows = [
        row
        for row in rows
        if "candidate" in " ".join(row.keys()).lower()
        or "source" in " ".join(row.keys()).lower()
    ]
    assert candidate_rows, "expected CSV rows describing candidate/source routes"

    candidate_text = "\n".join([text, *[row_text(row) for row in candidate_rows]])
    for term in EXPECTED_CANDIDATE_TERMS:
        assert re.search(re.escape(term), candidate_text, re.IGNORECASE), term


def test_ns_sprint91_no_allowed_source_supplies_both_required_inputs(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)

    allowed_source_rows = [
        row
        for row in rows
        if any(
            boolish(value) is True
            for key, value in row.items()
            if any(term in key.lower() for term in ("allowed", "admissible", "valid"))
        )
    ]
    assert allowed_source_rows, "audit should expose allowed/admissible source rows"

    offending_rows = []
    for row in allowed_source_rows:
        closes_pointwise_h1_tail = any(
            boolish(value) is True
            for key, value in row.items()
            if all(term in key.lower() for term in ("pointwise", "h1", "tail"))
        )
        supplies_independent_epsilon = any(
            boolish(value) is True
            for key, value in row.items()
            if "independent" in key.lower() and "epsilon" in key.lower()
        )
        if closes_pointwise_h1_tail and supplies_independent_epsilon:
            offending_rows.append(row)

    combined = text.lower()
    assert offending_rows == []
    assert "allowed source supplies both pointwise h1 tail and independent epsilon" not in combined

    count_values = values_matching_keys(summary, "allowed", "both")
    if count_values:
        assert not any(boolish(value) is True for value in count_values)


def test_ns_sprint91_route_decision_is_fail_closed_or_open(tmp_path: Path) -> None:
    _out_dir, summary, _rows, text = run_audit(tmp_path)

    decision = normalized(
        summary_value(
            summary,
            "route_decision",
            "decision",
            "final_route_decision",
            "audit_decision",
        )
    )
    assert decision in {"fail-closed", "fail-open", "open"}
    assert re.search(r"fail[-_ ]closed|fail[-_ ]open|\bopen\b", text, re.IGNORECASE)


def test_ns_sprint91_residual_gate_remains_pointwise_h1_tail_with_independent_epsilon(
    tmp_path: Path,
) -> None:
    _out_dir, summary, _rows, text = run_audit(tmp_path)

    residual_gate = summary_value(
        summary,
        "required_residual_gate",
        "residual_gate",
        "next_required_gate",
        "required_gate",
    )
    assert residual_gate == REQUIRED_RESIDUAL_GATE
    assert REQUIRED_RESIDUAL_GATE in text
