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
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint105_shell_density_classifier.py"
OUT_STEM = "ns_sprint105_shell_density_classifier"

EXPECTED_ROUTE_DECISION = "FAIL_CLOSED_SHELL_DENSITY_SOURCE"
REQUIRED_GATE_TERMS = (
    "lp_projector",
    "local_density_definition",
    "leray_integrability",
    "localization_bound",
    "non_circular_construction",
    "no_forbidden_dependency",
)
FORBIDDEN_DEPENDENCY_TERMS = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_density_locus",
    "imposed_shell_energy",
    "target_kstar_collapse",
)


def run_classifier(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    if not SCRIPT.exists():
        pytest.skip("Sprint105 shell density classifier script is not present.")

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
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "classifier did not write JSON output"
    assert md_paths, "classifier did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    rows: list[dict[str, Any]] = []
    if isinstance(summary.get("rows"), list):
        rows.extend(row for row in summary["rows"] if isinstance(row, dict))

    for path in json_paths:
        if path == summary_path:
            continue
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, list):
            rows.extend(row for row in payload if isinstance(row, dict))
        elif isinstance(payload, dict) and isinstance(payload.get("rows"), list):
            rows.extend(row for row in payload["rows"] if isinstance(row, dict))

    for path in sorted(out_dir.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    for path in [*json_paths, *sorted(out_dir.glob("*.csv")), *md_paths]:
        parts.append(path.read_text(encoding="utf-8"))
    return out_dir, summary, rows, "\n".join(parts)


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


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def combined_payload(summary: dict[str, Any], rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {"summary": summary, "rows": rows}


def candidate_name(candidate: dict[str, Any], fallback: int) -> str:
    for key in ("family", "candidate_family", "name", "candidate", "source_family"):
        value = candidate.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return f"candidate-{fallback}"


def unique_candidate_rows(summary: dict[str, Any], rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    candidates = summary.get("rows") if isinstance(summary.get("rows"), list) else []
    merged = [row for row in candidates if isinstance(row, dict)]
    merged.extend(row for row in rows if row not in merged)

    unique: dict[str, dict[str, Any]] = {}
    for index, candidate in enumerate(merged):
        unique.setdefault(candidate_name(candidate, index), candidate)
    return list(unique.values())


def sequence_value(candidate: dict[str, Any], key: str) -> list[str]:
    value = candidate.get(key)
    if isinstance(value, list):
        return [str(item) for item in value if str(item).strip()]
    if isinstance(value, tuple):
        return [str(item) for item in value if str(item).strip()]
    if isinstance(value, str):
        lowered = normalized(value)
        if lowered in {"", "none", "[]"}:
            return []
        return [part.strip() for part in re.split(r"[;,]", value) if part.strip()]
    return []


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint105_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_classifier(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*105|sprint105", text, re.IGNORECASE)
    assert re.search(r"shell", text, re.IGNORECASE)
    assert re.search(r"density", text, re.IGNORECASE)
    assert re.search(r"classif", text, re.IGNORECASE)


def test_ns_sprint105_routes_fail_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary.get("fail_closed") is True
    assert str(summary.get("route_decision", "")).upper() == EXPECTED_ROUTE_DECISION
    assert str(summary.get("final_decision", "")).upper() == EXPECTED_ROUTE_DECISION
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values)
    assert EXPECTED_ROUTE_DECISION in text
    assert re.search(r"zero|0", text, re.IGNORECASE)


def test_ns_sprint105_lists_required_gates_and_forbidden_dependencies(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined_text = json.dumps(combined_payload(summary, rows), sort_keys=True) + "\n" + text

    required_gates = summary.get("required_gates")
    forbidden_dependencies = summary.get("forbidden_dependencies")
    assert isinstance(required_gates, list) and required_gates
    assert isinstance(forbidden_dependencies, list) and forbidden_dependencies
    for term in REQUIRED_GATE_TERMS:
        assert normalized(term) in normalized(combined_text), term
    for term in FORBIDDEN_DEPENDENCY_TERMS:
        assert normalized(term) in normalized(combined_text), term


def test_ns_sprint105_rejects_all_five_candidate_families(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    candidates = unique_candidate_rows(summary, rows)

    assert summary.get("candidate_family_count") == 5
    assert len(candidates) == 5
    for candidate in candidates:
        assert boolish(candidate.get("accepted")) is not True
        assert re.search(r"reject|failed|fail-closed|blocked", json.dumps(candidate), re.IGNORECASE)

    assert re.search(r"reject", text, re.IGNORECASE)


def test_ns_sprint105_every_candidate_exposes_each_gate(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    candidates = unique_candidate_rows(summary, rows)
    required_gates = summary.get("required_gates")
    assert isinstance(required_gates, list) and required_gates

    for candidate in candidates:
        gate_results = candidate.get("gate_results")
        assert isinstance(gate_results, dict), candidate
        for gate in required_gates:
            assert gate in gate_results, {"candidate": candidate, "missing_gate": gate}
        assert sequence_value(candidate, "failed_gates")
        assert boolish(candidate.get("accepted")) is not True

    assert "gate" in normalized(text)


def test_ns_sprint105_keeps_clay_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)

    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values, "Clay boundary flag missing"
    assert not any(clay_values), clay_values
    assert summary.get("clay_navier_stokes_promoted") is False
    assert_no_true_assignment(text, "clay")
