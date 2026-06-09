from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint93_dominance_pointwise_coefficient_audit.py"
OUT_STEM = "ns_sprint93_dominance_pointwise_coefficient_audit"
REQUIRED_RESIDUAL_GATE = "DominanceWithPointwiseTailAndIndependentCoefficient"
REQUIRED_ANCHORS = (
    "dominance",
    "pointwise",
    "independent",
    "high-high",
    REQUIRED_RESIDUAL_GATE,
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    assert SCRIPT.exists(), "Sprint 93 dominance/pointwise/coefficient audit script is missing"

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
        if lowered in {"true", "1", "yes", "closed", "pass", "promoted", "accepted"}:
            return True
        if lowered in {"false", "0", "no", "open", "fail", "rejected", "not_promoted"}:
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


def combined_payload(summary: dict[str, Any], rows: list[dict[str, str]]) -> dict[str, Any]:
    return {"summary": summary, "csv_rows": rows}


def assert_false_key(payload: Any, text: str, *terms: str) -> None:
    values = values_for_key_terms(payload, *terms)
    bool_values = [parsed for parsed in (boolish(value) for value in values) if parsed is not None]
    assert bool_values, f"missing bool evidence for {'/'.join(terms)}"
    assert not any(bool_values), f"{'/'.join(terms)} unexpectedly true"

    assignment = re.compile(
        r"[\w -]*".join(re.escape(term) for term in terms)
        + r"[\w -]{0,80}[:=]\s*(true|1|yes|closed|promoted|accepted)\b",
        re.IGNORECASE,
    )
    assert not assignment.search(text), f"{'/'.join(terms)} unexpectedly promoted"


def test_ns_sprint93_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.csv"))
    assert sorted(out_dir.glob("*.md"))
    assert "sprint93" in text.lower() or "Sprint 93" in text


def test_ns_sprint93_required_anchors_are_present(tmp_path: Path) -> None:
    _out_dir, _summary, _rows, text = run_audit(tmp_path)

    for anchor in REQUIRED_ANCHORS:
        assert re.search(re.escape(anchor), text, re.IGNORECASE), anchor


def test_ns_sprint93_forbidden_count_is_zero(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    payload = combined_payload(summary, rows)

    counts = numeric_values_for_key_terms(payload, "forbidden", "count")
    assert counts, "audit output should expose a forbidden count"
    assert max(counts) == 0
    assert re.search(r"forbidden", text, re.IGNORECASE)


def test_ns_sprint93_inherited_bookkeeping_is_true(tmp_path: Path) -> None:
    _out_dir, summary, rows, _text = run_audit(tmp_path)
    payload = combined_payload(summary, rows)

    values = values_for_key_terms(payload, "inherited", "bookkeeping")
    bool_values = [parsed for parsed in (boolish(value) for value in values) if parsed is not None]
    assert bool_values, "audit should expose inherited bookkeeping evidence"
    assert all(bool_values)


def test_ns_sprint93_residual_gate_is_exact(tmp_path: Path) -> None:
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


def test_ns_sprint93_target_gates_and_clay_remain_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    payload = combined_payload(summary, rows)

    assert_false_key(payload, text, "dominance")
    assert_false_key(payload, text, "pointwise")
    assert_false_key(payload, text, "independent")
    assert_false_key(payload, text, "high", "high")
    assert_false_key(payload, text, "clay")
