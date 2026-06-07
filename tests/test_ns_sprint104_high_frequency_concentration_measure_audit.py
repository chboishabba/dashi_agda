from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint104_high_frequency_concentration_measure_audit.py"
OUT_STEM = "ns_sprint104_high_frequency_concentration_measure_audit"
EXPECTED_ROUTE_DECISION = "FAIL_CLOSED_HIGH_FREQUENCY_CONCENTRATION_MEASURE"
EXPECTED_MEASURE_SUBGATES = (
    "DyadicShellEnergyDensity",
    "ConcentrationThresholdSelection",
    "ConcentrationLocusMeasurability",
    "ScaleLocalizedTightness",
    "NonCircularConcentrationMeasureSource",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint104 high-frequency concentration measure audit script is missing"

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
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"

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
        elif isinstance(payload, dict):
            for key, value in payload.items():
                if isinstance(value, list):
                    rows.extend(
                        {"_json_name": path.name, "_row_group": key, **row}
                        for row in value
                        if isinstance(row, dict)
                    )

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    for path in [*json_paths, *md_paths]:
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
            "hold",
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


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint104_audit_writes_json_markdown_and_rows(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert rows, "high-frequency concentration measure audit should expose JSON rows"
    assert re.search(r"sprint\s*104|sprint104", text, re.IGNORECASE)
    assert re.search(r"high[_ -]?frequency", text, re.IGNORECASE)
    assert re.search(r"concentration", text, re.IGNORECASE)
    assert re.search(r"measure", text, re.IGNORECASE)
    assert re.search(r"\|[^|\n]*measure[^|\n]*\|", text, re.IGNORECASE)


def test_ns_sprint104_route_fails_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    route_decision = str(summary.get("route_decision", ""))

    assert summary["fail_closed"] is True
    assert summary["complete"] is False
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert route_decision.upper() == EXPECTED_ROUTE_DECISION
    assert str(summary.get("final_decision", "")).upper() == EXPECTED_ROUTE_DECISION

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values), fail_closed_values
    assert EXPECTED_ROUTE_DECISION in text


def test_ns_sprint104_measure_decomposition_closed_but_subgates_open(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    assert summary["decomposition_ledger_closed"] is True
    ledger_values = (
        bool_values_for_key_terms(combined, "measure", "decomposition", "ledger", "closed")
        or bool_values_for_key_terms(combined, "measure", "ledger", "closed")
        or bool_values_for_key_terms(combined, "ledger", "true")
    )
    assert ledger_values and all(ledger_values), ledger_values

    assert summary["all_subgates_false"] is True
    assert summary["all_subgates_closed"] is False
    assert summary["closed_subgate_count"] == 0

    for gate in EXPECTED_MEASURE_SUBGATES:
        assert gate in combined_text, gate
        gate_results = [
            item
            for item in rows + summary.get("gate_results", [])
            if isinstance(item, dict) and item.get("gate") == gate
        ]
        assert gate_results, gate
        assert all("recorded" in str(result.get("expected")) for result in gate_results)
        assert all("false" in str(result.get("expected")) for result in gate_results)
        assert all(result.get("passed") is True for result in gate_results), gate_results

    assert re.search(r"measure[_ -]?decomposition|ledger[_ -]?true", text, re.IGNORECASE)
    assert re.search(r"measure[_ -]?subgates?", combined_text, re.IGNORECASE)


def test_ns_sprint104_keeps_clay_false_and_unpromoted(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["clay_navier_stokes_promoted"] is False
    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values and not any(clay_values), clay_values
    assert_no_true_assignment(text, "clay")
