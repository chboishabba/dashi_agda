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
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint92_moving_kstar_boundary_audit.py"
OUT_STEM = "ns_sprint92_moving_kstar_boundary_audit"

REQUIRED_ANCHORS = (
    "frozen danger-time",
    "moving K* boundary",
    "pointwise H1 tail",
    "independent coefficient",
    "Clay",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 92 moving K* boundary audit script is not present.")

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
        if lowered in {"true", "1", "yes", "closed", "pass", "passed", "allowed", "promoted"}:
            return True
        if lowered in {"false", "0", "no", "open", "open-blocked", "fail", "failed", "blocked", "fail-closed", "not-promoted"}:
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


def require_bool(summary: dict[str, Any], expected: bool, *terms: str) -> None:
    values = matching_values(summary, *terms)
    assert values, f"missing summary key containing terms: {terms}"
    assert any(boolish(value) is expected for value in values), {
        "terms": terms,
        "values": values,
        "expected": expected,
    }


def require_zero(summary: dict[str, Any], *terms: str) -> None:
    values = matching_values(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    assert any(value == 0 or str(value).strip() == "0" for value in values), values


def route_decision(summary: dict[str, Any]) -> str:
    candidates = matching_values(summary, "route", "decision")
    candidates.extend(matching_values(summary, "summary", "route"))
    assert candidates, "missing summary route decision"
    normalized_candidates = {normalized(value) for value in candidates}
    assert normalized_candidates & {"open", "fail-closed"}, normalized_candidates
    return next(value for value in normalized_candidates if value in {"open", "fail-closed"})


def assert_no_positive_marker(summary: dict[str, Any], *terms: str) -> None:
    values = matching_values(summary, *terms)
    assert values, f"missing summary marker containing terms: {terms}"
    assert not any(boolish(value) is True for value in values), values


def test_ns_sprint92_writes_expected_artifacts_and_required_anchors(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))

    compact = re.sub(r"[\s_*`-]+", " ", text).lower()
    for anchor in REQUIRED_ANCHORS:
        assert re.sub(r"[\s_*`-]+", " ", anchor).lower() in compact, anchor


def test_ns_sprint92_summary_route_is_open_or_fail_closed_as_designed(tmp_path: Path) -> None:
    _out_dir, summary, _rows, text = run_audit(tmp_path)

    decision = route_decision(summary)
    assert decision in {"open", "fail-closed"}
    assert re.search(r"fail[-_ ]closed|\bopen\b", text, re.IGNORECASE)


def test_ns_sprint92_forbidden_count_zero_and_danger_time_bookkeeping_frozen(
    tmp_path: Path,
) -> None:
    _out_dir, summary, _rows, text = run_audit(tmp_path)

    require_zero(summary, "forbidden", "count")
    require_bool(summary, True, "frozen", "danger", "time")
    assert re.search(r"forbidden[^0-9]{0,40}0|0[^a-z0-9]{0,40}forbidden", text, re.IGNORECASE)


def test_ns_sprint92_boundary_theorem_and_coefficients_remain_unpromoted(
    tmp_path: Path,
) -> None:
    _out_dir, summary, _rows, _text = run_audit(tmp_path)

    assert_no_positive_marker(summary, "moving", "boundary", "theorem")
    assert_no_positive_marker(summary, "high", "high")
    assert_no_positive_marker(summary, "dominance")
    assert_no_positive_marker(summary, "pointwise")
    assert_no_positive_marker(summary, "independent", "coefficient")


def test_ns_sprint92_clay_promotion_false(tmp_path: Path) -> None:
    _out_dir, summary, _rows, text = run_audit(tmp_path)

    assert_no_positive_marker(summary, "clay")
    assert re.search(r"clay", text, re.IGNORECASE)
