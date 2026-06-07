from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint97_collapse_mechanism_classifier.py"
OUT_STEM = "ns_sprint97_collapse_mechanism_classifier"

REQUIRED_GATES = (
    "finite_time_kstar_to_zero",
    "low_mode_energy_concentration_dynamics",
    "viscous_damping_defeat_estimate",
    "leray_compatible_trajectory",
    "excludes_option_c_lower_bound",
    "singularity_extraction_without_bkm_or_serrin",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "blowup_construction_assumed",
    "clay_claim",
    "conditional_regular_negation",
    "desired_conclusion",
    "h1_continuation_failure_assumed",
    "option_c_lower_bound_negated_without_mechanism",
    "self_similarity_imposed_as_proof",
    "target_absorption",
    "target_blowup",
)


def run_classifier(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint97 collapse mechanism classifier script is missing"

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


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def combined_payload(summary: dict[str, Any], rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {"summary": summary, "rows": rows}


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint97_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_classifier(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*97|sprint97", text, re.IGNORECASE)
    assert re.search(r"collapse", text, re.IGNORECASE)
    assert re.search(r"mechanism", text, re.IGNORECASE)


def test_ns_sprint97_fails_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)

    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert summary.get("fail_closed") is True
    assert str(summary.get("route_decision", "")).upper() == "FAIL_CLOSED"
    assert str(summary.get("final_decision", "")).upper() == "FAIL_CLOSED"

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values)
    assert "FAIL_CLOSED" in text


def test_ns_sprint97_lists_all_required_gates(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    assert summary.get("required_gates") == list(REQUIRED_GATES)
    for gate in REQUIRED_GATES:
        assert normalized(gate) in normalized(combined_text), gate


def test_ns_sprint97_rejects_each_candidate_with_failed_gates_and_reasons(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    candidates = summary.get("rows") if isinstance(summary.get("rows"), list) else []
    candidates.extend(row for row in rows if row not in candidates)
    assert candidates, "classifier should expose candidate rejection records"

    for candidate in candidates:
        payload = json.dumps(candidate, sort_keys=True)
        assert re.search(r"reject|failed|fail-closed|blocked", payload, re.IGNORECASE), payload
        assert re.search(r"failed[-_ ]?gates?|gate", payload, re.IGNORECASE), payload
        assert re.search(r"reason|rationale|blocker|note", payload, re.IGNORECASE), payload
        assert boolish(candidate.get("accepted")) is not True

    assert re.search(r"failed[-_ ]?gates?|gate", text, re.IGNORECASE)
    assert re.search(r"reason|rationale|blocker|note", text, re.IGNORECASE)


def test_ns_sprint97_surfaces_forbidden_dependencies(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    assert values_for_key_terms(combined, "forbidden"), "forbidden dependency policy missing"
    for dependency in FORBIDDEN_DEPENDENCIES:
        assert normalized(dependency) in normalized(combined_text), dependency

    forbidden_records = [
        item
        for item in flatten(combined)
        if isinstance(item, dict)
        and re.search(r"forbidden|rejected|avoid", json.dumps(item), re.IGNORECASE)
    ]
    assert forbidden_records, "classifier should expose forbidden-dependency rejection evidence"
    assert not any(boolish(record.get("accepted")) is True for record in forbidden_records)


def test_ns_sprint97_does_not_promote_clay(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = combined_payload(summary, rows)

    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values, "classifier should expose Clay promotion state"
    assert not any(clay_values), clay_values
    assert re.search(r"clay", text, re.IGNORECASE)
    assert_no_true_assignment(text, "clay")
