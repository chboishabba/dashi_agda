from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint94_kstar_scaling_fork_audit.py"
OUT_STEM = "ns_sprint94_kstar_scaling_fork_audit"


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 94 kstar scaling fork audit script is missing"

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
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, result.stdout + result.stderr or "audit did not write JSON output"
    assert csv_paths, result.stdout + result.stderr or "audit did not write CSV output"
    assert md_paths, result.stdout + result.stderr or "audit did not write Markdown output"

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


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"true", "1", "yes", "pass", "ready", "open", "accepted"}:
            return True
        if lowered in {
            "false",
            "0",
            "no",
            "fail",
            "blocked",
            "not_ready",
            "not promoted",
            "not_promoted",
            "rejected",
        }:
            return False
    return None


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def payload(summary: dict[str, Any], rows: list[dict[str, str]]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": rows}


def test_ns_sprint94_writes_expected_output_surfaces(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*94|sprint94", text, re.IGNORECASE)
    assert re.search(r"k\*|kstar|Kstar|K\*", text)


def test_ns_sprint94_asserts_lower_bound_formula(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    formula_values = values_for_key_terms(combined, "lower", "bound")
    assert formula_values, "audit should expose a kstar lower-bound formula"

    formula_text = "\n".join(str(value) for value in formula_values) + "\n" + text
    assert re.search(r"K\*|kstar|k\*", formula_text)
    assert re.search(r">=|≥|lower[-_ ]bound", formula_text, re.IGNORECASE)
    assert re.search(r"nu|\bν\b", formula_text, re.IGNORECASE)
    assert re.search(r"H1|H\^1|tail|enstrophy|small[-_ ]data", formula_text, re.IGNORECASE)


def test_ns_sprint94_records_small_data_obstruction(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    obstruction_values = values_for_key_terms(combined, "small", "data")
    assert obstruction_values, "audit should expose the small-data obstruction"

    obstruction_text = "\n".join(str(value) for value in obstruction_values) + "\n" + text
    assert re.search(r"small[-_ ]data|small data", obstruction_text, re.IGNORECASE)
    assert re.search(r"obstruction|blocked|not[-_ ]available|requires|global", obstruction_text, re.IGNORECASE)
    assert not re.search(
        r"small[-_ ]data[\w -]{0,80}[:=]\s*(true|closed|proved|available|promoted)\b",
        obstruction_text,
        re.IGNORECASE,
    )


def test_ns_sprint94_conditional_route_ready_is_true(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    ready_values = bool_values_for_key_terms(combined, "conditional", "criterion", "ready")
    assert ready_values, "audit should expose conditional-route-ready as a bool"
    assert all(ready_values)
    assert summary.get("conditional_route") == "conditional_criterion_ready"
    assert re.search(
        r"conditional[-_ ]criterion[-_ ]ready|conditional route viable",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint94_does_not_promote_clay(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = payload(summary, rows)

    clay_values = bool_values_for_key_terms(combined, "clay", "promoted")
    assert clay_values, "audit should expose Clay promotion status"
    assert not any(clay_values)
    assert re.search(r"clay", text, re.IGNORECASE)
    assert not re.search(
        r"clay[\w -]{0,80}[:=]\s*(true|1|yes|closed|promoted|accepted)\b",
        text,
        re.IGNORECASE,
    )
