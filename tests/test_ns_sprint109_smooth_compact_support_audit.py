from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint109_smooth_compact_support_audit.py"
OUT_STEM = "ns_sprint109_smooth_compact_support_audit"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_ADMIT = "ad" + "mit"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_OPEN_WORK + r"(?![A-Za-z0-9_])"
    ),
    "incomplete implementation marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "empty framework marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_SKELETON + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "accepted-without-proof marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_ADMIT + r"(?:ted|s)?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "deferred proof wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "gap wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda open gap delimiter": re.compile(r"\{" + r"!|!" + r"\}"),
    "Agda open gap assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
    "Python ellipsis placeholder": re.compile(r"^\s*\.\.\.\s*(?:#.*)?$", re.MULTILINE),
    "Python pass placeholder": re.compile(r"^\s*pass\s*(?:#.*)?$", re.MULTILINE),
}


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint109 smooth compact support audit script is missing"

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
    rows = collect_rows(summary, json_paths, summary_path)

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    for path in [*json_paths, *md_paths]:
        parts.append(path.read_text(encoding="utf-8"))
    return out_dir, summary, rows, "\n".join(parts)


def collect_rows(
    summary: dict[str, Any], json_paths: list[Path], summary_path: Path
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for key in ("rows", "gate_results"):
        if isinstance(summary.get(key), list):
            rows.extend(row for row in summary[key] if isinstance(row, dict))

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
    return rows


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
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "accepted"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "fail-closed"}:
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


def subgate_rows(summary: dict[str, Any], rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    expected_names = summary.get("subgates")
    if not isinstance(expected_names, list):
        expected_names = []

    by_name: dict[str, dict[str, Any]] = {}
    for row in rows:
        name = str(row.get("gate") or row.get("name") or row.get("subgate") or "")
        if name in expected_names:
            by_name.setdefault(name, row)

    checks = summary.get("subgate_checks")
    if isinstance(checks, dict):
        for name, check in checks.items():
            if isinstance(check, dict):
                by_name.setdefault(str(name), {"gate": str(name), **check})

    return [by_name[name] for name in expected_names if name in by_name]


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def assert_no_forbidden_markers(text: str) -> None:
    failures = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            failures.append(f"{line}: {label}: {match.group(0)!r}")
    assert not failures, "Forbidden Sprint109 audit surface:\n" + "\n".join(failures)


def test_ns_sprint109_audit_writes_json_markdown_and_smooth_compact_support_rows(
    tmp_path: Path,
) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert rows or summary.get("subgate_checks"), "audit should expose JSON gate rows"
    assert re.search(r"sprint\s*109|sprint109", text, re.IGNORECASE)
    assert re.search(r"smooth[_ -]?compact[_ -]?support", text, re.IGNORECASE)
    assert re.search(r"\|[^|\n]*smooth[^|\n]*compact[^|\n]*support[^|\n]*\|", text, re.IGNORECASE)


def test_ns_sprint109_route_and_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["fail_closed"] is True
    assert summary["complete"] is False
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert "FAIL_CLOSED" in str(summary.get("route_decision", "")).upper()
    assert "SMOOTH" in str(summary.get("route_decision", "")).upper()
    assert "COMPACT" in str(summary.get("route_decision", "")).upper()
    assert str(summary.get("final_decision", "")).upper() == str(
        summary.get("route_decision", "")
    ).upper()

    fail_closed_values = bool_values_for_key_terms(combined, "fail", "closed")
    assert fail_closed_values and any(fail_closed_values), fail_closed_values
    assert str(summary["route_decision"]) in text


def test_ns_sprint109_evidence_audit_and_decomposition_ledger_are_true(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, _text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["evidence_audit_passed"] is True
    assert summary["decomposition_ledger_closed"] is True
    ledger_values = (
        bool_values_for_key_terms(
            combined, "smooth", "compact", "support", "decomposition", "ledger", "closed"
        )
        or bool_values_for_key_terms(combined, "decomposition", "ledger", "closed")
    )
    assert ledger_values and all(ledger_values), ledger_values


def test_ns_sprint109_five_subgates_present_and_open_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined_text = json.dumps(combined_payload(summary, rows), sort_keys=True) + "\n" + text

    assert isinstance(summary["subgates"], list)
    assert len(summary["subgates"]) == 5
    assert summary["all_subgates_false"] is True
    assert summary["all_subgates_closed"] is False
    assert summary["closed_subgate_count"] == 0
    assert summary["open_subgate_count"] == 5

    rows_by_gate = {row["gate"]: row for row in subgate_rows(summary, rows)}
    assert set(rows_by_gate) == set(summary["subgates"]), rows_by_gate
    for name in summary["subgates"]:
        row = rows_by_gate[name]
        row_text = json.dumps(row, sort_keys=True)
        assert re.search(r"open|false", row_text, re.IGNORECASE), row
        assert "false" in row_text.lower(), row
        assert not row.get("closed_true", False), row
        if "closed_false" in row:
            assert row["closed_false"] is True, row
        if "passed" in row:
            assert row["passed"] is True, row
        assert str(name) in combined_text


def test_ns_sprint109_downstream_and_clay_flags_false(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    downstream_values = (
        bool_values_for_key_terms(combined, "downstream", "ns")
        or bool_values_for_key_terms(combined, "navier", "stokes")
        or bool_values_for_key_terms(combined, "radial", "bump")
        or bool_values_for_key_terms(combined, "smooth", "dyadic", "cutoff")
    )
    assert downstream_values and not any(downstream_values), downstream_values

    clay_values = bool_values_for_key_terms(combined, "clay")
    assert clay_values and not any(clay_values), clay_values

    assert_no_true_assignment(text, "downstream", "ns")
    assert_no_true_assignment(text, "navier", "stokes")
    assert_no_true_assignment(text, "clay")


def test_ns_sprint109_has_no_forbidden_markers_in_outputs_or_script(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["forbidden_marker_count"] == 0
    assert summary["forbidden_hits"] == []
    forbidden_values = bool_values_for_key_terms(combined, "forbidden")
    assert forbidden_values and not any(forbidden_values), forbidden_values
    assert_no_forbidden_markers(text)

    source = SCRIPT.read_text(encoding="utf-8", errors="replace")
    assert_no_forbidden_markers(source)
    assert_no_true_assignment(source, "downstream", "ns")
    assert_no_true_assignment(source, "navier", "stokes")
    assert_no_true_assignment(source, "clay")
