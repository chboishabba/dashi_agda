from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint92_high_high_dominance_budget_audit.py"
OUT_STEM = "ns_sprint92_high_high_dominance_budget_audit"


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint 92 high-high dominance budget audit script is missing"

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

    summary_candidates = sorted(out_dir.glob("*summary*.json")) or sorted(
        out_dir.glob("*.json")
    )
    assert summary_candidates, result.stdout + result.stderr
    summary = json.loads(summary_candidates[0].read_text(encoding="utf-8"))
    return out_dir, summary, output_text(out_dir, summary)


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json.dumps(summary, sort_keys=True)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix.lower() in {".csv", ".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def csv_rows(out_dir: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in sorted(out_dir.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))
    return rows


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
        if lowered in {"true", "yes", "1", "present", "closed", "pass", "accepted"}:
            return True
        if lowered in {
            "false",
            "no",
            "0",
            "absent",
            "open",
            "fail",
            "rejected",
            "not_promoted",
        }:
            return False
    return None


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


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


def numeric_values_for_key_terms(payload: Any, *terms: str) -> list[int]:
    values: list[int] = []
    for value in values_for_key_terms(payload, *terms):
        if isinstance(value, bool):
            continue
        if isinstance(value, int):
            values.append(value)
        elif isinstance(value, str) and re.fullmatch(r"\d+", value.strip()):
            values.append(int(value.strip()))
        elif isinstance(value, list):
            values.append(len(value))
    return values


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def combined_payload(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": csv_rows(out_dir)}


def accepted_source_count(payload: Any, text: str) -> int:
    counts = numeric_values_for_key_terms(payload, "accepted", "source", "count")
    if counts:
        return max(counts)

    accepted_sources = [
        item
        for item in flatten(payload)
        if isinstance(item, dict)
        and re.search(r"source", json_text(item), re.IGNORECASE)
        and re.search(r"accepted|admitted", json_text(item), re.IGNORECASE)
        and not re.search(r"circular|forbidden|rejected", json_text(item), re.IGNORECASE)
    ]
    if accepted_sources:
        return len(accepted_sources)

    match = re.search(
        r"accepted[\w -]*source[\w -]*(?:count)?[^0-9]{0,40}([0-9]+)",
        text,
        re.IGNORECASE,
    )
    assert match, "audit output should expose an accepted-source count"
    return int(match.group(1))


def assert_no_true_flags(payload: Any, text: str, *terms: str) -> None:
    values = bool_values_for_key_terms(payload, *terms)
    assert values, f"missing bool evidence for {'/'.join(terms)}"
    assert not any(values)

    pattern = re.compile(
        r"[\w -]*".join(re.escape(term) for term in terms)
        + r"[\w -]{0,80}[:=]\s*(true|1|yes|closed|promoted)\b",
        re.IGNORECASE,
    )
    assert not pattern.search(text), f"{'/'.join(terms)} unexpectedly true/closed"


def test_ns_sprint92_writes_markdown_json_and_csv_outputs(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json")), "audit did not write JSON output"
    assert sorted(out_dir.glob("*.csv")), "audit did not write CSV output"
    assert sorted(out_dir.glob("*.md")), "audit did not write Markdown output"
    assert "sprint92" in text.lower() or "Sprint 92" in text


def test_ns_sprint92_accepts_no_circular_or_forbidden_sources(
    tmp_path: Path,
) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    payload = combined_payload(out_dir, summary)
    combined_text = "\n".join([text, *[json_text(row) for row in csv_rows(out_dir)]])

    assert accepted_source_count(payload, combined_text) == 0
    assert re.search(r"circular|non[-_ ]circular", combined_text, re.IGNORECASE)
    assert re.search(r"forbidden", combined_text, re.IGNORECASE)

    rejected = [
        item
        for item in flatten(payload)
        if isinstance(item, dict)
        and re.search(r"forbidden", json_text(item), re.IGNORECASE)
        and re.search(r"reject|fail[-_ ]closed|blocked", json_text(item), re.IGNORECASE)
    ]
    assert rejected, "forbidden dependencies should be explicitly rejected"


def test_ns_sprint92_residual_gate_is_exactly_recorded(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    payload = combined_payload(out_dir, summary)
    combined_text = "\n".join([text, *[json_text(row) for row in csv_rows(out_dir)]])

    residual_values = values_for_key_terms(payload, "residual", "gate")
    assert residual_values, "audit should expose the residual gate"

    residual_text = " ".join(str(value) for value in residual_values) + "\n" + combined_text
    assert re.search(r"\bexact(?:ly)?\b|exactly[-_ ]recorded", residual_text, re.IGNORECASE)
    assert not re.search(
        r"residual[\w -]*gate[\w -]{0,80}[:=]\s*(closed|true|promoted|accepted)\b",
        residual_text,
        re.IGNORECASE,
    )


def test_ns_sprint92_high_high_and_dominance_gates_stay_open(
    tmp_path: Path,
) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    payload = combined_payload(out_dir, summary)
    combined_text = "\n".join([text, *[json_text(row) for row in csv_rows(out_dir)]])

    assert_no_true_flags(payload, combined_text, "high", "high", "gate")
    assert_no_true_flags(payload, combined_text, "dominance", "gate")


def test_ns_sprint92_clay_is_not_promoted(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    payload = combined_payload(out_dir, summary)
    combined_text = "\n".join([text, *[json_text(row) for row in csv_rows(out_dir)]])

    clay_values = values_for_key_terms(payload, "clay") + values_for_key_terms(
        payload, "promoted"
    )
    assert clay_values, "audit should expose Clay promotion evidence"
    assert not any(boolish(value) is True for value in clay_values)
    assert re.search(
        r"clay[^.\n]*(false|not[-_ ]promoted|no promotion)|no Clay promotion",
        combined_text,
        re.IGNORECASE,
    )
    assert not re.search(
        r"\b(clay[_ -]?navier[_ -]?stokes[_ -]?promoted|clay|promotion|promoted)"
        r"\b[\w -]{0,40}[:=]\s*(true|1|yes)\b",
        combined_text,
        re.IGNORECASE,
    )
