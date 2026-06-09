from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint132_gap_inventory_classifier.py"
STEM = "ns_sprint132_gap_inventory_classifier"
OUT_DIR = REPO_ROOT / "outputs" / STEM
SUMMARY_NAME = STEM + "_summary.json"
ROWS_NAME = STEM + "_rows.json"
REPORT_NAME = STEM + ".md"

EXPECTED_TIER_COUNTS = {
    "closed_exact": 4,
    "conditionally_closed": 2,
    "open": 5,
}
EXPECTED_CLOSED_EXACT = {
    "anti-correlation",
    "Gram matrix",
    "multi-packet Reynolds stress",
    "zero-mean rotation cycle",
}
EXPECTED_CONDITIONALLY_CLOSED = {
    "vortex-stretching log-gap obstruction",
    "Hou-Luo viscous obstruction beta>0",
}
EXPECTED_OPEN = {
    "large-Re axisymmetric",
    "marginal beta=0",
    "Euler nu=0",
    "non-resonant triads",
    "multi-scale concentration",
}
EXPECTED_PUBLISHABLE_NOW = {
    "WBF no-go tower",
    "axisymmetric moderate-Re regularization",
}
SINGLE_LOAD_BEARING_MISSING = "NoLogAxisymmetricBiotSavartUniform"
RECOMMENDED_NEXT_ACTION = "attempt_NoLogAxisymmetricBiotSavartUniform"

CLAY_TRUE_PATTERNS = (
    re.compile(r'(?<![A-Za-z0-9_])"?clay"?(?![A-Za-z0-9_])\s*[:=]\s*(?:true|1)\b', re.IGNORECASE),
    re.compile(r'(?<![A-Za-z0-9_])"?clay_promoted"?(?![A-Za-z0-9_])\s*[:=]\s*(?:true|1)\b', re.IGNORECASE),
    re.compile(r'(?<![A-Za-z0-9_])"?clay_navier_stokes_promoted"?(?![A-Za-z0-9_])\s*[:=]\s*(?:true|1)\b', re.IGNORECASE),
    re.compile(r'(?<![A-Za-z0-9_])"?full_clay_ns_solved"?(?![A-Za-z0-9_])\s*[:=]\s*(?:true|1)\b', re.IGNORECASE),
    re.compile(r"\bClay\s+Navier[- ]Stokes\s+(?:promoted|solved)\b\s*[:=]\s*(?:true|1)\b", re.IGNORECASE),
)
CLAY_FLAG_KEY = re.compile(
    r"^(?:clay|clay_promoted|clay_navier_stokes_promoted|full_clay_ns_solved)$",
    re.IGNORECASE,
)


def run_classifier() -> tuple[subprocess.CompletedProcess[str], dict[str, Any], Any, str]:
    assert SCRIPT.is_file(), f"missing Sprint132 gap inventory classifier: {SCRIPT.relative_to(REPO_ROOT)}"

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

    summary_path = OUT_DIR / SUMMARY_NAME
    rows_path = OUT_DIR / ROWS_NAME
    report_path = OUT_DIR / REPORT_NAME
    artifact_paths = [path for path in (summary_path, rows_path, report_path) if path.exists()]
    output_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in artifact_paths]
    )

    assert result.returncode == 0, output_text
    assert summary_path.is_file(), output_text
    assert rows_path.is_file(), output_text
    assert report_path.is_file(), output_text
    assert all(path.stat().st_size > 0 for path in (summary_path, rows_path, report_path))

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    rows = json.loads(rows_path.read_text(encoding="utf-8"))
    assert isinstance(summary, dict) and summary, "summary JSON must be a nonempty object"
    return result, summary, rows, output_text


def walk(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for child in value.values() for item in walk(child)]
    if isinstance(value, list):
        return [value] + [item for child in value for item in walk(child)]
    return [value]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def tier_count(summary: dict[str, Any], tier: str) -> int:
    direct_keys = (tier + "_count", tier + "_tier_count")
    for key in direct_keys:
        value = summary.get(key)
        if isinstance(value, int):
            return value

    for map_key in ("tier_counts", "counts_by_tier", "gap_tier_counts"):
        value = summary.get(map_key)
        if isinstance(value, dict) and isinstance(value.get(tier), int):
            return value[tier]

    raise AssertionError(f"summary does not expose an integer count for tier {tier!r}: {json_text(summary)}")


def tier_items(summary: dict[str, Any], rows: Any, tier: str) -> set[str]:
    found: set[str] = set()
    candidate_keys = (
        tier,
        tier + "_items",
        tier + "_lemmas",
        tier + "_gaps",
        tier + "_names",
    )
    for payload in (summary, rows):
        for item in walk(payload):
            if isinstance(item, dict):
                for key, value in item.items():
                    if str(key) in candidate_keys:
                        found.update(string_items(value))
                if row_tier(item) == tier:
                    found.update(row_names(item))
    return found


def string_items(value: Any) -> set[str]:
    if isinstance(value, str):
        return {value}
    if isinstance(value, dict):
        return {
            item
            for child in value.values()
            for item in string_items(child)
        }
    if isinstance(value, list):
        return {
            item
            for child in value
            for item in string_items(child)
        }
    return set()


def row_tier(row: dict[str, Any]) -> str | None:
    for key in ("tier", "classification", "status", "gap_tier"):
        value = row.get(key)
        if isinstance(value, str) and value in EXPECTED_TIER_COUNTS:
            return value
    return None


def row_names(row: dict[str, Any]) -> set[str]:
    names = set()
    for key in ("name", "item", "lemma", "gap", "gap_name", "gate", "id", "row_id", "theorem"):
        value = row.get(key)
        if isinstance(value, str):
            names.add(value)
    return names


def value_for_key(payload: Any, key: str) -> Any:
    matches = [
        item[key]
        for item in walk(payload)
        if isinstance(item, dict) and key in item
    ]
    assert matches, f"missing key {key!r} in payload: {json_text(payload)}"
    return matches[0]


def clay_bool_rows(payload: Any) -> list[dict[str, Any]]:
    return [
        item
        for item in walk(payload)
        if isinstance(item, dict)
        and any(
            isinstance(value, bool)
            and CLAY_FLAG_KEY.search(str(key))
            for key, value in item.items()
        )
    ]


def test_sprint132_gap_inventory_cli_writes_expected_outputs_directory() -> None:
    _result, summary, rows, output_text = run_classifier()

    assert OUT_DIR.is_dir(), f"expected script to write {OUT_DIR.relative_to(REPO_ROOT)}"
    assert summary.get("contract", STEM) == STEM
    assert rows, "rows JSON must contain the gap inventory"
    assert "gap" in output_text.lower() or "inventory" in output_text.lower()


def test_sprint132_gap_inventory_records_tier_counts_and_named_items() -> None:
    _result, summary, rows, output_text = run_classifier()

    for tier, expected_count in EXPECTED_TIER_COUNTS.items():
        assert tier_count(summary, tier) == expected_count, output_text

    assert EXPECTED_CLOSED_EXACT <= tier_items(summary, rows, "closed_exact"), output_text
    assert EXPECTED_CONDITIONALLY_CLOSED <= tier_items(summary, rows, "conditionally_closed"), output_text
    assert EXPECTED_OPEN <= tier_items(summary, rows, "open"), output_text


def test_sprint132_gap_inventory_identifies_single_load_bearing_missing_lemma() -> None:
    _result, summary, rows, output_text = run_classifier()

    assert value_for_key(summary, "single_load_bearing_missing_lemma") == SINGLE_LOAD_BEARING_MISSING
    assert value_for_key(summary, "recommended_next_action") == RECOMMENDED_NEXT_ACTION

    text = json_text([summary, rows])
    assert SINGLE_LOAD_BEARING_MISSING in text, output_text
    assert RECOMMENDED_NEXT_ACTION in text, output_text

    conditional_rows = [
        row
        for row in walk(rows)
        if isinstance(row, dict)
        and row.get("classification") == "conditionally_closed"
    ]
    assert len(conditional_rows) == 2, output_text
    assert all(row.get("missing_lemma") == SINGLE_LOAD_BEARING_MISSING for row in conditional_rows)


def test_sprint132_gap_inventory_publishable_now_contains_two_papers() -> None:
    _result, summary, rows, output_text = run_classifier()

    publishable_now = value_for_key(summary, "publishable_now")
    publishable_text = json_text(publishable_now)
    assert isinstance(publishable_now, list), output_text
    assert len(publishable_now) == 2, output_text
    for paper in EXPECTED_PUBLISHABLE_NOW:
        assert paper in publishable_text, output_text

    all_text = json_text([summary, rows])
    for paper in EXPECTED_PUBLISHABLE_NOW:
        assert paper in all_text, output_text


def test_sprint132_gap_inventory_keeps_all_clay_flags_false() -> None:
    _result, summary, rows, output_text = run_classifier()
    payload = [summary, rows]

    clay_rows = clay_bool_rows(payload)
    assert clay_rows, "classifier must expose explicit Clay/Navier-Stokes non-promotion flags"
    assert not any(
        value is True
        for row in clay_rows
        for key, value in row.items()
        if isinstance(value, bool)
        and CLAY_FLAG_KEY.search(str(key))
    ), json_text(clay_rows)

    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(output_text), pattern.pattern
