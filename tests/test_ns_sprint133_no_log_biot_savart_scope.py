from __future__ import annotations

import csv
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint133_no_log_biot_savart_scope.py"
STEM = "ns_sprint133_no_log_biot_savart_scope"
OUT_DIR = REPO_ROOT / "outputs" / STEM
LEMMA = "NoLogAxisymmetricBiotSavartUniform"

CLAY_FLAG_KEYS = {
    "clay",
    "clay_promoted",
    "clay_navier_stokes_promoted",
    "claynavierstokespromoted",
    "full_clay_ns_solved",
    "fullclaynssolved",
}
CLAY_TRUE_PATTERN = re.compile(
    r'(?<![A-Za-z0-9_])"?'
    r"(?:clay|clay_promoted|clay_navier_stokes_promoted|"
    r"clayNavierStokesPromoted|full_clay_ns_solved)"
    r'"?(?![A-Za-z0-9_])\s*[:=]\s*(?:true|1)\b',
    re.IGNORECASE,
)
PROGRESS_KEYS = {
    "clay_progress_estimate",
    "clay_progress_estimate_percent",
    "clay_completion_delta",
    "clay_progress_delta",
    "estimated_clay_progress",
    "clay_needle_movement",
    "clay_needle_movement_percent",
    "full_clay_progress_estimate",
}


def run_scope_script() -> tuple[dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.is_file(), f"missing Worker 3 Sprint133 script: {SCRIPT.relative_to(REPO_ROOT)}"

    shutil.rmtree(OUT_DIR, ignore_errors=True)
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(OUT_DIR),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    json_paths = sorted(OUT_DIR.glob("*.json"))
    csv_paths = sorted(OUT_DIR.glob("*.csv"))
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in json_paths]
        + [path.read_text(encoding="utf-8", errors="replace") for path in csv_paths]
    )

    assert result.returncode == 0, artifact_text
    assert json_paths, artifact_text
    assert csv_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in json_paths + csv_paths)

    json_payloads = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in json_paths
    ]
    csv_rows: list[dict[str, Any]] = []
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            csv_rows.extend(dict(row) for row in csv.DictReader(handle))

    summary_candidates = [payload for payload in json_payloads if isinstance(payload, dict)]
    assert summary_candidates, "expected at least one JSON object summary"
    rows = flatten_rows(json_payloads) + csv_rows
    assert rows, "expected JSON or CSV rows describing scoped consequences"

    merged_summary: dict[str, Any] = {}
    for payload in summary_candidates:
        merged_summary.update(payload)
    return merged_summary, rows, artifact_text


def flatten_rows(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        rows: list[dict[str, Any]] = []
        for key in ("rows", "scope_rows", "gap_rows", "subcases", "cases", "claims"):
            child = value.get(key)
            if isinstance(child, list):
                rows.extend(item for item in child if isinstance(item, dict))
        if looks_like_row(value):
            rows.append(value)
        for child in value.values():
            rows.extend(flatten_rows(child))
        return rows
    if isinstance(value, list):
        return [row for child in value for row in flatten_rows(child)]
    return []


def looks_like_row(value: dict[str, Any]) -> bool:
    if set(value) == {"key", "value"}:
        return False
    row_keys = {
        "row_id",
        "case",
        "subcase",
        "scope",
        "mechanism_class",
        "status",
        "classification",
        "closes",
        "closed_by_a1",
        "after_a1",
        "gap_name",
    }
    return bool(row_keys.intersection(value))


def walk(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for child in value.values() for item in walk(child)]
    if isinstance(value, list):
        return [value] + [item for child in value for item in walk(child)]
    return [value]


def joined_text(*payloads: Any) -> str:
    return "\n".join(
        json.dumps(payload, sort_keys=True, default=str)
        if not isinstance(payload, str)
        else payload
        for payload in payloads
    )


def normalize(text: Any) -> str:
    return str(text).lower().replace("_", "-").replace(" ", "-")


def numeric_zero(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, (int, float)):
        return value == 0
    if isinstance(value, str):
        stripped = value.strip().lower()
        return stripped in {"0", "0.0", "0%", "0 percent", "zero", "approximately 0%"}
    return False


def row_mentions(row: dict[str, Any], *needles: str) -> bool:
    text = normalize(joined_text(row))
    return all(normalize(needle) in text for needle in needles)


def row_is_closed_subcase(row: dict[str, Any]) -> bool:
    if not {"row_id", "route_class", "regime"}.intersection(row):
        return False
    if not row_mentions(row, "AXS"):
        return False
    if not (row_mentions(row, "beta>0") or row_mentions(row, "beta gt 0")):
        return False
    if not (row_mentions(row, "moderate") or row_mentions(row, "one subcase")):
        return False
    text = normalize(joined_text(row))
    return any(marker in text for marker in ("closed", "unconditional", "true"))


def explicit_false_clay_flags(summary: dict[str, Any], rows: list[dict[str, Any]]) -> list[tuple[str, bool]]:
    flags: list[tuple[str, bool]] = []
    for item in walk(summary) + walk(rows):
        if isinstance(item, dict):
            for key, value in item.items():
                normalized_key = str(key).replace("_", "").lower()
                if str(key).lower() in CLAY_FLAG_KEYS or normalized_key in CLAY_FLAG_KEYS:
                    assert value is False or str(value).lower() == "false", (
                        f"Clay promotion flag {key!r} must be false, got {value!r}"
                    )
                    flags.append((str(key), False))
    return flags


def test_sprint133_no_log_scope_writes_json_and_csv_outputs() -> None:
    summary, rows, artifact_text = run_scope_script()

    assert OUT_DIR.is_dir(), artifact_text
    assert summary.get("contract", STEM) == STEM
    assert LEMMA in artifact_text
    assert rows


def test_sprint133_no_log_records_zero_clay_progress_estimate() -> None:
    summary, rows, artifact_text = run_scope_script()

    progress_values = [
        item[key]
        for item in walk(summary) + walk(rows)
        if isinstance(item, dict)
        for key in PROGRESS_KEYS
        if key in item
    ]
    assert progress_values, "expected an explicit Clay progress estimate field"
    assert all(numeric_zero(value) for value in progress_values), progress_values
    assert "approximately 0" in artifact_text.lower() or any(
        numeric_zero(value) for value in progress_values
    )


def test_sprint133_no_log_closes_only_one_axisymmetric_subcase() -> None:
    summary, rows, artifact_text = run_scope_script()

    closed_count_candidates = [
        item[key]
        for item in walk(summary)
        if isinstance(item, dict)
        for key in ("closed_subcase_count", "subcases_closed_count", "a1_closed_subcase_count")
        if key in item
    ]
    if closed_count_candidates:
        assert all(value == 1 for value in closed_count_candidates), closed_count_candidates

    closed_rows_by_id = {
        row.get("row_id", json.dumps(row, sort_keys=True)): row
        for row in rows
        if row_is_closed_subcase(row)
    }
    closed_rows = list(closed_rows_by_id.values())
    assert len(closed_rows) == 1, artifact_text
    assert row_mentions(closed_rows[0], "CLASS AXS") or row_mentions(closed_rows[0], "AXS")
    assert row_mentions(closed_rows[0], "beta>0") or row_mentions(closed_rows[0], "beta gt 0")


def test_sprint133_no_log_leaves_beta_zero_and_large_re_open() -> None:
    _summary, rows, artifact_text = run_scope_script()

    case_rows = [
        row
        for row in rows
        if {"row_id", "route_class", "regime"}.intersection(row)
    ]
    beta_zero_rows = [row for row in case_rows if row_mentions(row, "beta=0") or row_mentions(row, "beta eq 0")]
    large_re_rows = [row for row in case_rows if row_mentions(row, "large-Re") or row_mentions(row, "large Re")]
    assert beta_zero_rows, artifact_text
    assert large_re_rows, artifact_text

    for row in beta_zero_rows + large_re_rows:
        text = normalize(joined_text(row))
        assert any(marker in text for marker in ("open", "still-open", "untouched", "not-closed")), row
        assert not row_is_closed_subcase(row), row


def test_sprint133_no_log_leaves_outside_wbf_axs_untouched() -> None:
    _summary, rows, artifact_text = run_scope_script()

    outside_rows = [
        row
        for row in rows
        if row_mentions(row, "outside WBF/AXS")
        or row_mentions(row, "outside WBF")
        or row_mentions(row, "mechanisms outside")
    ]
    assert outside_rows, artifact_text
    for row in outside_rows:
        text = normalize(joined_text(row))
        assert any(marker in text for marker in ("untouched", "open", "not-advanced", "not-closed")), row


def test_sprint133_no_log_keeps_clay_promotion_false_everywhere() -> None:
    summary, rows, artifact_text = run_scope_script()

    assert not CLAY_TRUE_PATTERN.search(artifact_text), artifact_text
    flags = explicit_false_clay_flags(summary, rows)
    assert flags, "expected explicit Clay promotion booleans set to false"
