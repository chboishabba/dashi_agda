from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint113_crow_persistence_audit.py"
OUT_STEM = "ns_sprint113_crow_persistence_audit"
EXPECTED_ROUTE = "CROW_PERSISTENCE_UNDER_NSE_LEDGER_CLOSED_FAIL_CLOSED_NO_PROMOTION"
EXPECTED_BLOCKED_DECISION = "FAIL_CLOSED_AUDIT_BLOCKED"

REQUIRED_ANCHORS = (
    "NSSprint113CrowPersistenceUnderNSEvolution",
    "canonicalNSSprint113CrowPersistenceUnderNSEvolution",
    "nsSprint113CrowPersistenceUnderNSEvolutionReceipt",
    "canonicalNSSprint113CrowPersistenceUnderNSEvolutionReceipt",
    "canonicalCrowPersistenceUnderNSEvolutionReceipt",
    "canonicalCrowPersistenceUnderNSEvolutionFlags",
    "ImportedSprint112Anchor",
    "canonicalImportedSprint112Anchor",
    "PersistenceTimescaleStatement",
    "canonicalPersistenceTimescaleStatement",
    "PersistenceSubgateStatuses",
    "canonicalPersistenceSubgateStatuses",
    "crowPersistenceUnderNSEvolutionLedgerClosed",
    "initialCrowDominanceImported",
)

REQUIRED_STRINGS = (
    "T_persist >= c / gamma_Crow",
    "initial linear Crow dominance",
    "NSE persistence",
)

EXPECTED_TRUE_FLAGS = (
    "crowPersistenceUnderNSEvolutionLedgerClosed",
    "initialCrowDominanceImported",
)

EXPECTED_FALSE_FLAGS = (
    "crowGrowthPersistenceUnderNSEvolutionClosed",
    "nonlinearDeformationControlClosed",
    "viscousDecayWindowClosed",
    "ellipticModeLeakageControlClosed",
    "persistenceTimescaleLowerBoundClosed",
    "positiveFluxAccumulationWindowClosed",
    "ellipticBackreactionBound",
    "FiniteTimeFluxSurplusFromCrowDominance",
    "strainCompressionAtHighFrequencyConcentrationPointsClosed",
    "clayNavierStokesPromoted",
)

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
    assert SCRIPT.exists(), "Sprint113 Crow persistence audit script is missing"

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
    for key in ("rows", "gate_results", "anchor_checks", "promotion_flags"):
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


def combined_payload(summary: dict[str, Any], rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {"summary": summary, "rows": rows}


def category_values(summary: dict[str, Any], category: str) -> list[bool]:
    category_flag_checks = summary.get("category_flag_checks")
    assert isinstance(category_flag_checks, dict)
    checks = category_flag_checks.get(category)
    assert isinstance(checks, dict), category
    values = list(checks.values())
    assert all(isinstance(value, bool) for value in values), category
    return values


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
    assert not failures, "Forbidden Sprint113 audit surface:\n" + "\n".join(failures)


def test_ns_sprint113_audit_runs_and_writes_json_markdown(tmp_path: Path) -> None:
    out_dir, summary, rows, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert rows or summary.get("anchor_checks") or summary.get("promotion_flags")
    assert re.search(r"sprint\s*113|sprint113", text, re.IGNORECASE)
    assert re.search(r"crow[-_ ]?persistence|persistence[-_ ]?audit", text, re.IGNORECASE)


def test_ns_sprint113_route_status_and_exact_flags(tmp_path: Path) -> None:
    _out_dir, summary, rows, text = run_audit(tmp_path)
    combined = combined_payload(summary, rows)

    assert summary["route_decision"] == EXPECTED_ROUTE
    assert summary["final_decision"] in {EXPECTED_ROUTE, EXPECTED_BLOCKED_DECISION}
    assert summary["fail_closed"] is (summary["final_decision"] == EXPECTED_BLOCKED_DECISION)
    assert summary["promotion_decision"] == "hold"
    assert summary["promotion_hold"] is True

    bool_checks = summary["bool_checks"]
    assert set(bool_checks) == {*EXPECTED_TRUE_FLAGS, *EXPECTED_FALSE_FLAGS}
    for key in EXPECTED_TRUE_FLAGS:
        check = bool_checks[key]
        assert check["expected"] is True, key
        assert check["actual"] == "true", key
        assert check["passed"] is True, key
    for key in EXPECTED_FALSE_FLAGS:
        check = bool_checks[key]
        assert check["expected"] is False, key
        assert check["actual"] == "false", key
        assert check["passed"] is True, key

    assert summary["proof_claimed"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["analytic_flags_false"] is True
    assert summary["downstream_flags_false"] is True
    assert summary["clay_flags_false"] is True

    persistence_values = bool_values_for_key_terms(combined, "crow", "persistence")
    assert persistence_values and any(persistence_values), persistence_values
    for category in ("analytic", "downstream", "clay"):
        values = category_values(summary, category)
        assert all(values), (category, values)
    assert EXPECTED_ROUTE in text
    assert "FAIL_CLOSED" in text


def test_ns_sprint113_required_anchors_strings_and_markdown_report(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_audit(tmp_path)

    anchors = summary.get("required_anchors")
    assert isinstance(anchors, list)
    anchor_text = "\n".join(str(anchor) for anchor in anchors) + "\n" + text
    for anchor in REQUIRED_ANCHORS:
        assert re.search(re.escape(anchor), anchor_text, re.IGNORECASE), anchor

    required_strings = summary.get("required_strings")
    assert isinstance(required_strings, list)
    string_text = "\n".join(str(item) for item in required_strings) + "\n" + text
    for required in REQUIRED_STRINGS:
        assert re.search(re.escape(required), string_text, re.IGNORECASE), required

    md_paths = sorted(out_dir.glob("*.md"))
    assert md_paths, "audit did not write Markdown output"
    report_text = "\n".join(path.read_text(encoding="utf-8") for path in md_paths)
    assert re.search(r"^# .*Sprint\s*113", report_text, re.IGNORECASE | re.MULTILINE)
    assert re.search(r"route|status|gate", report_text, re.IGNORECASE)
    assert re.search(r"Crow\s+persistence|persistence", report_text, re.IGNORECASE)
    assert re.search(r"Clay\s+NS|Clay\s+Navier[- ]Stokes|Clay", report_text, re.IGNORECASE)
    assert re.search(r"promotion[^.\n]*(false|hold|no[_ -]?promotion)", report_text, re.IGNORECASE)


def test_ns_sprint113_analytic_downstream_clay_flags_remain_false_everywhere(
    tmp_path: Path,
) -> None:
    _out_dir, summary, _rows, _text = run_audit(tmp_path)

    for category in ("analytic", "downstream", "clay"):
        values = category_values(summary, category)
        assert all(values), (category, values)

    clay_check = summary["bool_checks"]["clayNavierStokesPromoted"]
    assert clay_check["expected"] is False
    assert clay_check["actual"] == "false"
    assert clay_check["passed"] is True

    source = SCRIPT.read_text(encoding="utf-8", errors="replace")
    assert_no_true_assignment(source, "analytic")
    assert_no_true_assignment(source, "downstream")
    assert_no_true_assignment(source, "clay", "navier", "stokes")
    assert_no_true_assignment(source, "clay", "promotion")
    assert_no_true_assignment(source, "navier", "stokes", "promoted")


def test_ns_sprint113_has_no_forbidden_markers_in_outputs_or_script(
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
