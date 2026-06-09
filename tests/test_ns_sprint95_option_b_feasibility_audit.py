from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint95_option_b_feasibility_audit.py"
OUT_STEM = "ns_sprint95_option_b_feasibility_audit"

REQUIRED_ANCHORS = (
    "NSSprint95",
    "Sprint95",
    "OptionB",
    "Feasibility",
    "optionBFeasibilityLedgerClosed",
    "Sprint94",
    "fail_closed",
    "Clay",
    "blowup",
)

OPEN_GATE_TERMS = (
    ("conditional", "criterion"),
    ("general", "data"),
    ("clay",),
    ("blowup",),
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 95 Option B feasibility audit script is missing"

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

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    parts.extend(path.read_text(encoding="utf-8") for path in [*json_paths, *csv_paths, *md_paths])
    return out_dir, summary, rows, "\n".join(parts)


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
        if lowered in {"true", "1", "yes", "closed", "pass", "passed", "ready", "accepted"}:
            return True
        if lowered in {
            "false",
            "0",
            "no",
            "open",
            "fail",
            "failed",
            "blocked",
            "not_ready",
            "not_promoted",
            "rejected",
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


def combined_payload(summary: dict[str, Any], rows: list[dict[str, str]]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": rows}


def assert_bool_evidence(
    combined: dict[str, Any],
    text: str,
    expected: bool,
    *terms: str,
) -> None:
    values = bool_values_for_key_terms(combined, *terms)
    assert values, f"missing bool evidence for {'/'.join(terms)}"
    assert expected in values, f"{'/'.join(terms)} never recorded as {expected}"

    unexpected = "false" if expected else "true"
    assignment = re.compile(
        r"[\w -]*".join(re.escape(term) for term in terms)
        + rf"[\w -]{{0,100}}[:=]\s*{unexpected}\b",
        re.IGNORECASE,
    )
    assert not assignment.search(text), f"{'/'.join(terms)} unexpectedly recorded as {unexpected}"


def test_ns_sprint95_option_b_writes_json_csv_and_markdown(tmp_path: Path) -> None:
    out_dir, summary, rows, _text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "audit CSV outputs should expose rows"


def test_ns_sprint95_option_b_required_anchors_are_reported(tmp_path: Path) -> None:
    _out_dir, _summary, _rows, text = run_audit(tmp_path)

    for anchor in REQUIRED_ANCHORS:
        assert re.search(re.escape(anchor), text, re.IGNORECASE), anchor


def test_ns_sprint95_option_b_terminal_flags_fail_closed_not_complete(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["fail_closed"] is True
    assert summary["complete"] is False
    assert_bool_evidence(combined, text, True, "fail", "closed")
    assert_bool_evidence(combined, text, False, "complete")


def test_ns_sprint95_option_b_does_not_promote_clay_or_blowup(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["blowup_construction_closed"] is False
    assert_bool_evidence(combined, text, False, "clay")
    assert_bool_evidence(combined, text, False, "blowup")


def test_ns_sprint95_option_b_ledger_closed_and_open_gates_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["optionBFeasibilityLedgerClosed"] is True
    assert_bool_evidence(combined, text, True, "optionBFeasibilityLedgerClosed")

    for terms in OPEN_GATE_TERMS:
        assert_bool_evidence(combined, text, False, *terms)


def test_ns_sprint95_option_b_inherits_sprint94_state(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["sprint94_inherited"] is True
    assert_bool_evidence(combined, text, True, "Sprint94", "inherited")
