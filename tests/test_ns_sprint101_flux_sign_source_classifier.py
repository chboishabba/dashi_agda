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
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint101_flux_sign_source_classifier.py"
OUT_STEM = "ns_sprint101_flux_sign_source_classifier"
EXPECTED_ROUTE_DECISION = "FAIL_CLOSED_FLUX_SIGN_SOURCE"
REQUIRED_GATES = (
    "triadic_sign_coherence",
    "low_mode_projection_sign_control",
    "cancellation_defect_bound",
    "pressure_transport_sign_accounting",
    "leray_energy_compatible",
    "non_circular_flux_sign_source",
    "no_forbidden_dependency",
)
FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_flux_sign",
    "imposed_triad_phase",
    "target_kstar_collapse",
    "imposed_surplus_window",
)


def run_classifier(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    if not SCRIPT.exists():
        pytest.skip("Sprint101 flux sign source classifier script is not present.")

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


def test_ns_sprint101_writes_classifier_outputs(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_classifier(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*101|sprint101", text, re.IGNORECASE)
    assert re.search(r"flux", text, re.IGNORECASE)
    assert re.search(r"sign", text, re.IGNORECASE)
    assert re.search(r"source", text, re.IGNORECASE)


def test_ns_sprint101_fails_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary.get("fail_closed") is True
    assert str(summary.get("route_decision", "")).upper() == EXPECTED_ROUTE_DECISION
    assert str(summary.get("final_decision", "")).upper() == EXPECTED_ROUTE_DECISION
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values)
    assert EXPECTED_ROUTE_DECISION in text


def test_ns_sprint101_lists_exact_required_gates_and_forbidden_deps(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined_text = json.dumps(combined_payload(summary, rows), sort_keys=True) + "\n" + text

    assert summary.get("required_gates") == list(REQUIRED_GATES)
    assert summary.get("forbidden_dependencies") == list(FORBIDDEN_DEPENDENCIES)
    for gate in REQUIRED_GATES:
        assert normalized(gate) in normalized(combined_text), gate
    for dependency in FORBIDDEN_DEPENDENCIES:
        assert normalized(dependency) in normalized(combined_text), dependency


def test_ns_sprint101_rejects_all_six_candidate_families(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    candidates = unique_candidate_rows(summary, rows)
    required_gates = {normalized(gate) for gate in REQUIRED_GATES}
    forbidden_dependencies = {normalized(dependency) for dependency in FORBIDDEN_DEPENDENCIES}

    assert summary.get("candidate_family_count") == 6
    assert len(candidates) == 6
    for candidate in candidates:
        failed_gates = sequence_value(candidate, "failed_gates")
        blocked_dependencies = sequence_value(candidate, "forbidden_dependencies")
        payload = json.dumps(candidate, sort_keys=True)

        assert re.search(r"reject|failed|fail-closed|blocked", payload, re.IGNORECASE), payload
        assert re.search(r"reason|rationale|blocker|note", payload, re.IGNORECASE), payload
        assert boolish(candidate.get("accepted")) is not True
        assert failed_gates or blocked_dependencies, payload
        assert all(normalized(gate) in required_gates for gate in failed_gates), failed_gates
        assert all(
            normalized(dependency) in forbidden_dependencies for dependency in blocked_dependencies
        ), blocked_dependencies

    assert re.search(r"six|6", text, re.IGNORECASE)
    assert re.search(r"candidate[-_ ]famil", text, re.IGNORECASE)


def test_ns_sprint101_keeps_option_b_open_and_clay_unpromoted(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)

    option_b_values = bool_values_for_key_terms(combined, "option", "b", "closed")
    assert option_b_values, "Option B closure flag missing"
    assert not any(option_b_values), option_b_values
    assert summary.get("option_b_closed") is False
    assert_no_true_assignment(text, "option", "b", "closed")

    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values, "Clay boundary flag missing"
    assert not any(clay_values), clay_values
    assert_no_true_assignment(text, "clay")
