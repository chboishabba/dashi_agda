from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint93_candidate_source_matrix_audit.py"
OUT_STEM = "ns_sprint93_candidate_source_matrix_audit"

FORBIDDEN_DEPENDENCIES = (
    "h1_continuation",
    "serrin",
    "bkm",
    "target_absorption",
    "theta_preservation",
    "clay",
    "desired_conclusion",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 93 candidate source matrix audit script is not present.")

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

    artifact_text = "\n".join(
        [json.dumps(summary, sort_keys=True)]
        + [path.read_text(encoding="utf-8") for path in [*json_paths, *csv_paths, *md_paths]]
        + [result.stdout, result.stderr]
    )
    return out_dir, summary, rows, artifact_text


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
        if lowered in {"true", "1", "yes", "pass", "passed", "allowed", "accepted", "promoted"}:
            return True
        if lowered in {
            "false",
            "0",
            "no",
            "fail",
            "failed",
            "blocked",
            "rejected",
            "fail-closed",
            "not-promoted",
        }:
            return False
    return None


def matching_values(summary: dict[str, Any], *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if all(pattern.search(str(key)) for pattern in patterns):
                values.append(value)
    return values


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = matching_values(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def row_bool(row: dict[str, str], *terms: str) -> bool | None:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    for key, value in row.items():
        if all(pattern.search(key) for pattern in patterns):
            parsed = boolish(value)
            if parsed is not None:
                return parsed
    return None


def row_int(row: dict[str, str], *terms: str) -> int | None:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    for key, value in row.items():
        if all(pattern.search(key) for pattern in patterns) and value.strip().isdigit():
            return int(value.strip())
    return None


def row_text(row: dict[str, str], *terms: str) -> str:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    return " ".join(value for key, value in row.items() if all(pattern.search(key) for pattern in patterns))


def test_ns_sprint93_candidate_source_matrix_outputs_exist(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "candidate source matrix should contain at least one candidate row"
    assert re.search(r"candidate|source|matrix", text, re.IGNORECASE)


def test_ns_sprint93_accepted_source_count_is_zero_without_complete_allowed_source(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, _text = run_audit(tmp_path)

    accepted_count = numeric_summary_value(summary, "accepted", "source", "count")
    complete_allowed_rows = [
        row
        for row in rows
        if row_bool(row, "accepted") is True
        or (
            row_bool(row, "allowed") is True
            and row_bool(row, "complete") is True
            and row_bool(row, "forbidden") is False
        )
    ]

    if complete_allowed_rows:
        assert accepted_count == len(complete_allowed_rows)
    else:
        assert accepted_count == 0


def test_ns_sprint93_forbidden_dependencies_are_rejected(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)

    assert re.search(r"forbidden|rejected|fail[-_ ]closed", text, re.IGNORECASE)
    assert matching_values(summary, "forbidden"), "summary should record forbidden dependency policy"

    forbidden_rows = [
        row
        for row in rows
        if (row_int(row, "forbidden", "count") or 0) > 0
        or any(token in normalized(row_text(row, "forbidden") + " " + row_text(row, "depend")) for token in FORBIDDEN_DEPENDENCIES)
    ]
    assert forbidden_rows, "matrix should include at least one forbidden-dependency rejection row"
    assert all(row_bool(row, "accepted") is not True and row_bool(row, "allowed") is not True for row in forbidden_rows)


def test_ns_sprint93_same_source_rule_is_enforced(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)

    assert re.search(r"same[-_ ]source|single[-_ ]source|same source", text, re.IGNORECASE)
    assert matching_values(summary, "same", "source"), "summary should record same-source policy"

    split_source_rows = [
        row
        for row in rows
        if re.search(r"split|different|separate|not[-_ ]same|multi", json.dumps(row), re.IGNORECASE)
    ]
    assert split_source_rows, "matrix should exercise rejection of split-source candidates"
    assert all(row_bool(row, "accepted") is not True and row_bool(row, "allowed") is not True for row in split_source_rows)


def test_ns_sprint93_residual_gate_recorded_and_clay_not_promoted(tmp_path: Path) -> None:
    _out_dir, summary, _rows, text = run_audit(tmp_path)

    assert matching_values(summary, "residual", "gate"), "summary should record the residual gate"
    assert re.search(r"residual[^.\n]{0,80}gate|gate[^.\n]{0,80}residual", text, re.IGNORECASE)

    clay_values = matching_values(summary, "clay")
    assert clay_values, "summary should expose Clay promotion state"
    assert not any(boolish(value) is True for value in clay_values), clay_values
    assert re.search(r"clay", text, re.IGNORECASE)
