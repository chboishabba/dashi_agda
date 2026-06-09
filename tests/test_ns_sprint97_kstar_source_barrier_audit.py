from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint97_kstar_source_barrier_audit.py"
OUT_STEM = "ns_sprint97_kstar_source_barrier_audit"
ROUTE_DECISION = "FAIL_CLOSED_KSTAR_SOURCE_BARRIER"

REQUIRED_ANCHORS = (
    "NSSprint97KStarCollapseSourceBarrier",
    "canonicalNSSprint97KStarCollapseSourceBarrier",
    "Sprint97",
    "KStarCollapseSourceBarrier",
    "KStarCollapseSourceBarrierResiduals",
    "KStarSourceBarrier",
    "failClosedKStarSourceBarrier",
    "FAIL_CLOSED_KSTAR_SOURCE_BARRIER",
    "same_source_collapse_mechanism_available",
    "accepted_source_count",
)

REQUIRED_ANALYTIC_OBJECTS = (
    ("k", "star", "source", "barrier"),
    ("same", "source", "collapse", "mechanism"),
    ("accepted", "source", "count"),
    ("route", "decision"),
    ("fail", "closed"),
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 97 K* source barrier audit script is missing"

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


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def combined_payload(summary: dict[str, Any], rows: list[dict[str, str]]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": rows}


def assert_text_contains(text: str, needle: str) -> None:
    pattern = re.escape(needle).replace(r"\ ", r"[- _]*")
    assert re.search(pattern, text, re.IGNORECASE), needle


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint97_audit_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "source barrier audit should expose CSV rows"
    assert re.search(r"sprint\s*97|sprint97", text, re.IGNORECASE)
    assert re.search(r"k\*|kstar|k-star|K\*", text)


def test_ns_sprint97_audit_fails_closed_without_completion(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["fail_closed"] is True
    assert summary["complete"] is False
    assert summary["route_decision"] == ROUTE_DECISION
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert "FAIL_CLOSED_KSTAR_SOURCE_BARRIER" in text

    fail_closed_values = [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(combined, "fail", "closed"))
        if parsed is not None
    ]
    assert fail_closed_values and any(fail_closed_values), fail_closed_values


def test_ns_sprint97_same_source_collapse_mechanism_is_unavailable(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["same_source_collapse_mechanism_available"] is False
    same_source_values = [
        parsed
        for parsed in (
            boolish(value)
            for value in values_for_key_terms(combined, "same", "source", "collapse", "mechanism")
        )
        if parsed is not None
    ]
    assert same_source_values and not any(same_source_values), same_source_values
    assert_no_true_assignment(text, "same", "source", "collapse", "mechanism")


def test_ns_sprint97_required_anchors_and_analytic_objects_are_surfaced(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    for anchor in REQUIRED_ANCHORS:
        assert_text_contains(combined_text, anchor)

    for terms in REQUIRED_ANALYTIC_OBJECTS:
        assert values_for_key_terms(combined, *terms) or re.search(
            r"[\w *-]{0,80}".join(re.escape(term) for term in terms),
            combined_text,
            re.IGNORECASE,
        ), terms


def test_ns_sprint97_does_not_promote_clay(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    clay_values = [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(combined, "clay"))
        if parsed is not None
    ]
    assert clay_values, "audit should expose Clay promotion state"
    assert not any(clay_values), clay_values
    assert re.search(r"clay", text, re.IGNORECASE)
    assert_no_true_assignment(text, "clay")
