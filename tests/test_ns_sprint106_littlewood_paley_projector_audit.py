from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint106_littlewood_paley_projector_audit.py"
OUT_STEM = "ns_sprint106_littlewood_paley_projector_audit"
EXPECTED_ROUTE_DECISION = "FAIL_CLOSED_LITTLEWOOD_PALEY_SHELL_PROJECTOR"
EXPECTED_PROJECTOR_SUBGATES = (
    "SmoothDyadicCutoffPartition",
    "FourierMultiplierBoundedness",
    "LerayCompatibleProjection",
    "DivergenceFreeProjectionCommutation",
    "NonCircularProjectorConstruction",
)

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
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
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "incomplete implementation marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])",
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
    "dummy wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "deferred proof wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "hole wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Python ellipsis placeholder": re.compile(r"^\s*\.\.\.\s*(?:#.*)?$", re.MULTILINE),
    "Python pass placeholder": re.compile(r"^\s*pass\s*(?:#.*)?$", re.MULTILINE),
}


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint106 Littlewood-Paley projector audit script is missing"

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


def projector_subgate_rows(summary: dict[str, Any], rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    candidates = [
        row
        for row in rows + summary.get("gate_results", [])
        if isinstance(row, dict)
        and str(row.get("gate", "")) in EXPECTED_PROJECTOR_SUBGATES
    ]
    named: dict[str, dict[str, Any]] = {}
    for row in candidates:
        gate = str(row.get("gate") or row.get("name") or row.get("subgate") or "")
        if gate:
            named.setdefault(gate, row)
    return list(named.values())


def test_ns_sprint106_audit_writes_json_markdown_and_projector_rows(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert rows or summary.get("gate_results"), "audit should expose JSON gate rows"
    assert re.search(r"sprint\s*106|sprint106", text, re.IGNORECASE)
    assert re.search(r"littlewood[_ -]?paley", text, re.IGNORECASE)
    assert re.search(r"projector", text, re.IGNORECASE)
    assert re.search(r"\|[^|\n]*projector[^|\n]*\|", text, re.IGNORECASE)


def test_ns_sprint106_route_fails_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
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


def test_ns_sprint106_decomposition_ledger_true_but_projector_subgates_open(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)
    combined_text = json.dumps(combined, sort_keys=True) + "\n" + text

    assert summary["decomposition_ledger_closed"] is True
    ledger_values = (
        bool_values_for_key_terms(combined, "projector", "decomposition", "ledger", "closed")
        or bool_values_for_key_terms(combined, "decomposition", "ledger", "closed")
        or bool_values_for_key_terms(combined, "ledger", "true")
    )
    assert ledger_values and all(ledger_values), ledger_values

    assert summary["all_subgates_false"] is True
    assert summary["all_subgates_closed"] is False
    assert summary["closed_subgate_count"] == 0
    assert summary["open_subgate_count"] == 5

    subgate_rows = projector_subgate_rows(summary, rows)
    assert len(subgate_rows) == 5, subgate_rows
    for row in subgate_rows:
        row_text = json.dumps(row, sort_keys=True)
        assert re.search(r"open|false", row_text, re.IGNORECASE), row
        assert "false" in row_text.lower(), row
        if "passed" in row:
            assert row["passed"] is True, row

    assert re.search(r"projector[_ -]?decomposition|ledger[_ -]?true", combined_text, re.IGNORECASE)
    assert re.search(r"projector[_ -]?subgates?", combined_text, re.IGNORECASE)


def test_ns_sprint106_keeps_downstream_ns_flags_false_and_unpromoted(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    downstream_values = (
        bool_values_for_key_terms(combined, "downstream", "ns")
        or bool_values_for_key_terms(combined, "navier", "stokes")
    )
    assert downstream_values and not any(downstream_values), downstream_values

    promotion_values = (
        bool_values_for_key_terms(combined, "promoted")
        or bool_values_for_key_terms(combined, "promotion")
    )
    assert promotion_values and not any(promotion_values), promotion_values

    assert_no_true_assignment(text, "downstream", "ns")
    assert_no_true_assignment(text, "navier", "stokes")
    assert_no_true_assignment(text, "promot")


def test_ns_sprint106_script_has_no_forbidden_markers_or_true_promotion_flags() -> None:
    assert SCRIPT.exists(), "Sprint106 Littlewood-Paley projector audit script is missing"
    source = SCRIPT.read_text(encoding="utf-8", errors="replace")

    failures = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(f"{SCRIPT.relative_to(REPO_ROOT)}:{line}: {label}")

    assert not failures, "Forbidden Sprint106 audit script surface:\n" + "\n".join(failures)
    assert_no_true_assignment(source, "downstream", "ns")
    assert_no_true_assignment(source, "navier", "stokes")
    assert_no_true_assignment(source, "promot")
