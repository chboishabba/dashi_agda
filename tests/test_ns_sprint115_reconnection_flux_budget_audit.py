from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint115_reconnection_flux_budget_audit.py"
OUT_STEM = "ns_sprint115_reconnection_flux_budget_audit"
TARGET_AGDA = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint115ReconnectionFluxBudget.agda"
)

EXPECTED_ROUTE = "RECONNECTION_FLUX_BUDGET_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION"
EXPECTED_TRUE_FLAGS = (
    "sprint115ReconnectionFluxBudgetLedgerClosed",
    "sprint114ThinCoreCorrectionImported",
    "fluxIntegralFormulaRecorded",
    "reconnectionTimescaleRecorded",
    "viscousReynoldsConditionRecorded",
    "kstarCollapseThresholdRecorded",
)
EXPECTED_FALSE_FLAGS = (
    "reconnectionWindowLowerBoundClosed",
    "viscousDecayWindowClosed",
    "nonlinearDeformationControlClosed",
    "positiveFluxAccumulationWindowClosed",
    "finiteTimeFluxSurplusFromCrowDominance",
    "finiteKStarCollapseClosed",
    "blowupCriterionBridgeClosed",
    "clayNavierStokesPromoted",
)
REQUIRED_STRINGS = (
    "Sprint 115 quantitative reconnection-window flux budget.",
    "It closes only the formula ledger.",
    "FluxBudget = integral_0_to_T_reconnect Pi_HH_to_L(t) dt",
    "Re_delta = Gamma / nu >> b^2 / delta^2",
    "FluxBudget >= KStarCollapseThreshold",
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


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint115 reconnection flux budget audit script is missing"

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
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    text_parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    text_parts.extend(path.read_text(encoding="utf-8") for path in json_paths + md_paths)
    return out_dir, summary, "\n".join(text_parts)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def boolish(value: object) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        lowered = value.strip().replace("_", "-").lower()
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "hold"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "fail-closed"}:
            return False
    return None


def values_for_key_terms(payload: Any, *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(payload):
        if isinstance(item, dict):
            values.extend(
                value
                for key, value in item.items()
                if all(pattern.search(str(key)) for pattern in patterns)
            )
    return values


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def assert_no_forbidden_markers(text: str) -> None:
    failures = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            failures.append(f"{line}: {label}: {match.group(0)!r}")
    assert not failures, "Forbidden Sprint115 audit surface:\n" + "\n".join(failures)


def assert_no_true_assignment(text: str, *terms: str) -> None:
    prefix = r"[\w *-]{0,80}".join(re.escape(term) for term in terms)
    assert not re.search(
        prefix + r"[\w *-]{0,120}[:=]\s*(true|1|yes|closed|accepted|promoted)\b",
        text,
        re.IGNORECASE,
    )


def test_ns_sprint115_audit_exists_runs_and_writes_json_markdown(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    for required in REQUIRED_STRINGS:
        assert re.search(re.escape(required), text, re.IGNORECASE), required


def test_ns_sprint115_route_flags_and_no_clay_promotion(tmp_path: Path) -> None:
    _out_dir, summary, text = run_audit(tmp_path)

    assert summary["route_decision"] == EXPECTED_ROUTE
    assert summary.get("promotion_decision") == "hold"
    assert summary.get("promotion_hold") is True

    bool_checks = summary["bool_checks"]
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

    clay_check = summary["bool_checks"]["clayNavierStokesPromoted"]
    assert clay_check["actual"] == "false"
    assert clay_check["passed"] is True
    assert_no_true_assignment(text, "clay", "navier", "stokes")
    assert_no_true_assignment(text, "clay", "promotion")


def test_ns_sprint115_has_no_forbidden_markers_in_outputs_script_or_target_agda(
    tmp_path: Path,
) -> None:
    _out_dir, summary, text = run_audit(tmp_path)

    assert summary["forbidden_marker_count"] == 0
    assert summary["forbidden_hits"] == []
    assert_no_forbidden_markers(text)

    source = SCRIPT.read_text(encoding="utf-8", errors="replace")
    assert_no_forbidden_markers(source)
    assert_no_true_assignment(source, "clay", "navier", "stokes")
    assert_no_true_assignment(source, "clay", "promotion")

    assert TARGET_AGDA.exists(), "Sprint115 reconnection flux budget target Agda file is missing"
    target_text = TARGET_AGDA.read_text(encoding="utf-8", errors="replace")
    assert_no_forbidden_markers(target_text)
    assert_no_true_assignment(target_text, "clay", "navier", "stokes")
    assert_no_true_assignment(target_text, "clay", "promotion")
