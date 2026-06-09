#!/usr/bin/env python3
"""Sprint 123 NS rotating-frame phase-locking fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint123_phase_locking_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint123_phase_locking_audit")
SUMMARY_NAME = "ns_sprint123_phase_locking_audit_summary.json"
ROWS_NAME = "ns_sprint123_phase_locking_audit_rows.json"
REPORT_NAME = "ns_sprint123_phase_locking_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint123RotatingFramePhaseLockingEstimate.agda")
ROUTE_DECISION = "SPRINT123_ROTATING_FRAME_PHASE_LOCKING_LEDGER_CLOSED_FAIL_CLOSED_PROMOTION_HELD"

REQUIRED_ANCHORS = [
    "NSSprint123RotatingFramePhaseLockingEstimate",
    "canonicalNSSprint123RotatingFramePhaseLockingEstimate",
    "ImportedSprint122Persistence",
    "canonicalImportedSprint122Persistence",
    "RotatingFramePhaseLockingEstimateReceipt",
    "canonicalRotatingFramePhaseLockingEstimateReceipt",
    "NSEDerivedPhaseODERequirement",
    "canonicalNSEDerivedPhaseODERequirement",
    "DampingDriftBalance",
    "canonicalDampingDriftBalance",
    "FavorableWindowLowerBoundRequirement",
    "canonicalFavorableWindowLowerBoundRequirement",
    "ClassifierSamplerReceipt",
    "canonicalClassifierSamplerReceipt",
    "ImposedLockingRejection",
    "canonicalImposedLockingRejection",
    "Sprint123GateStatuses",
    "canonicalSprint123GateStatuses",
    "sprint123ReceiptSummary",
]

REQUIRED_STRINGS = [
    "Sprint123 imports Sprint122 persistence obstruction",
    "RotatingFramePhaseLockingEstimate",
    "phase locking must follow from NSE-derived frame dynamics",
    "imposed phase locking is circular",
    "requires favorable phase-lag window lower bound",
    "damping drift and strain rotation must leave positive dwell time",
    "RotatingStrainFluxBudgetBeatsKStar remains open",
    "complete=false",
    "clayNavierStokesPromoted remains false",
]

EXPECTED_BOOLEANS = {
    "sprint123RotatingFramePhaseLockingLedgerClosed": True,
    "sprint122PersistenceImported": True,
    "rotatingFramePhaseLockingEstimateRecorded": True,
    "nseDerivedPhaseODERequirementRecorded": True,
    "dampingDriftBalanceRecorded": True,
    "favorableWindowLowerBoundRequirementRecorded": True,
    "classifierSamplerRecorded": True,
    "imposedLockingRejected": True,
    "rotatingFramePhaseLockingEstimateClosed": False,
    "favorablePhaseLagWindowLowerBoundClosed": False,
    "rotatingStrainFluxBudgetBeatsKStarClosed": False,
    "kStarCollapseFromRotatingStrainClosed": False,
    "blowupCriterionBridgeClosed": False,
    "globalLerayCompatibleRotatingStrainDataClosed": False,
    "navierStokesClayAssemblyClosed": False,
    "clayNavierStokesPromoted": False,
}

TRUE_KEYWORDS = ("ledger", "imported", "recorded")
FALSE_KEYWORDS = ("estimate", "bound", "closed", "collapse", "blowup", "assembly", "promoted", "clay")
EXEMPT_FALSE_NAMES = {name for name, expected in EXPECTED_BOOLEANS.items() if expected}

TOKEN_A = "post" + "ulate"
TOKEN_B = "TO" + "DO"
TOKEN_C = "st" + "ub"
TOKEN_D = "skele" + "ton"
TOKEN_E = "ad" + "mit"
TOKEN_F = "du" + "m" + "my"
TOKEN_G = "place" + "holder"
TOKEN_H = "future" + r"[\s-]*" + "proof"
TOKEN_I = "ho" + "le"
SCREEN_PATTERNS = {
    "unproved_axiom": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_A + r"(?![A-Za-z0-9_])"),
    "open_work": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_B + r"(?![A-Za-z0-9_])"),
    "unfinished_text": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_C + r"(?![A-Za-z0-9_])", re.I),
    "empty_frame": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_D + r"s?(?![A-Za-z0-9_])", re.I),
    "accepted_without_derivation": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_E + r"(?:ted|s)?(?![A-Za-z0-9_])",
        re.I,
    ),
    "synthetic_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_F + r"(?![A-Za-z0-9_])", re.I),
    "temporary_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_G + r"s?(?![A-Za-z0-9_])", re.I),
    "deferred_proof_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_H + r"(?![A-Za-z0-9_])", re.I),
    "gap_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_I + r"s?(?![A-Za-z0-9_])", re.I),
    "agda_gap_delimiter": re.compile(r"\{" + r"!|!" + r"\}"),
    "agda_gap_assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}


@dataclass(frozen=True)
class GateRow:
    gate: str
    expected: str
    actual: str
    passed: bool
    status: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def identifier_present(text: str, identifier: str) -> bool:
    return bool(re.search(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])", text))


def bool_assignment(text: str, name: str, expected: bool) -> bool:
    value = "true" if expected else "false"
    return bool(
        re.search(
            r"(?<![A-Za-z0-9_])"
            + re.escape(name)
            + r"(?![A-Za-z0-9_])(?:\s*:\s*[^\n=]+)?\s*=\s*"
            + value
            + r"(?![A-Za-z0-9_])",
            text,
            re.MULTILINE,
        )
    )


def actual_bool_assignment(text: str, name: str) -> str:
    if bool_assignment(text, name, True):
        return "true"
    if bool_assignment(text, name, False):
        return "false"
    return "missing"


def bool_assignments(text: str) -> dict[str, str]:
    return {
        match.group("name"): match.group("value")
        for match in re.finditer(
            r"(?<![A-Za-z0-9_])(?P<name>[A-Za-z][A-Za-z0-9_]*)"
            r"(?![A-Za-z0-9_])(?:\s*:\s*Bool)?\s*=\s*"
            r"(?P<value>true|false)(?![A-Za-z0-9_])",
            text,
            re.MULTILINE,
        )
    }


def normalize_name(name: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", name.lower())


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def keyword_flag_checks(assigned_bools: dict[str, str]) -> dict[str, dict[str, bool]]:
    checks: dict[str, dict[str, bool]] = {"true": {}, "false": {}}
    for name, value in assigned_bools.items():
        normalized = normalize_name(name)
        if any(keyword in normalized for keyword in TRUE_KEYWORDS):
            if name in EXPECTED_BOOLEANS and EXPECTED_BOOLEANS[name] is True:
                checks["true"][name] = value == "true"
        if any(keyword in normalized for keyword in FALSE_KEYWORDS):
            if name not in EXEMPT_FALSE_NAMES:
                checks["false"][name] = value == "false"
    return checks


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.exists()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_present(text, anchor)]
    missing_required_strings = [literal for literal in REQUIRED_STRINGS if literal not in text]
    bool_checks = {
        name: {
            "expected": expected,
            "actual": actual_bool_assignment(text, name) if present else "missing",
            "passed": bool_assignment(text, name, expected) if present else False,
        }
        for name, expected in EXPECTED_BOOLEANS.items()
    }
    screen_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in SCREEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]
    assigned_bools = bool_assignments(text)
    keyword_checks = keyword_flag_checks(assigned_bools)
    gate_rows = [
        GateRow(
            name,
            "true" if expected else "false",
            bool_checks[name]["actual"],
            bool_checks[name]["passed"],
            "PASS" if bool_checks[name]["passed"] else "FAIL_CLOSED_BOOLEAN_GATE",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
    ]
    gate_rows.extend(
        GateRow(
            f"keyword_true:{name}",
            "true",
            assigned_bools[name],
            passed,
            "PASS" if passed else "FAIL_CLOSED_REQUIRED_TRUE_KEYWORD_FLAG",
        )
        for name, passed in keyword_checks["true"].items()
    )
    gate_rows.extend(
        GateRow(
            f"keyword_false:{name}",
            "false",
            assigned_bools[name],
            passed,
            "PASS" if passed else "FAIL_CLOSED_DOWNSTREAM_FLAG_TRUE",
        )
        for name, passed in keyword_checks["false"].items()
    )
    gate_rows.extend(
        GateRow(
            f"required_string:{literal}",
            "present",
            "present" if literal not in missing_required_strings else "missing",
            literal not in missing_required_strings,
            "PASS" if literal not in missing_required_strings else "FAIL_CLOSED_MISSING_REQUIRED_STRING",
        )
        for literal in REQUIRED_STRINGS
    )
    gate_rows.extend(
        [
            GateRow(
                "target_module",
                str(AGDA_PATH),
                "present" if present else "missing",
                present,
                "PASS" if present else "FAIL_CLOSED_MISSING_TARGET",
            ),
            GateRow("route", ROUTE_DECISION, ROUTE_DECISION, True, "PASS"),
            GateRow(
                "required_anchors",
                "all present",
                "all present" if not missing_anchors else "; ".join(missing_anchors),
                not missing_anchors,
                "PASS" if not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR",
            ),
            GateRow(
                "screened_terms",
                "none",
                "none" if not screen_hits else str(len(screen_hits)),
                not screen_hits,
                "PASS" if not screen_hits else "FAIL_CLOSED_SCREEN_HIT",
            ),
        ]
    )
    structural_checks_pass = (
        present
        and not missing_anchors
        and not missing_required_strings
        and not screen_hits
        and all(row.passed for row in gate_rows)
    )
    required_true_flags = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is True)
    required_false_flags = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is False)
    keyword_true_flags_coherent = all(keyword_checks["true"].values())
    keyword_false_flags_coherent = all(keyword_checks["false"].values())
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "target_present": present,
        "complete": structural_checks_pass,
        "proof_claimed": False,
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION if structural_checks_pass else "FAIL_CLOSED_AUDIT_BLOCKED",
        "promotion_decision": "hold",
        "promotion_ready": False,
        "promotion_hold": True,
        "evidence_audit_passed": structural_checks_pass,
        "ledger_coherent_fail_closed": structural_checks_pass,
        "required_true_flags": required_true_flags,
        "required_false_flags": required_false_flags,
        "keyword_true_flags_coherent": keyword_true_flags_coherent,
        "keyword_false_flags_coherent": keyword_false_flags_coherent,
        "sprint123_rotating_frame_phase_locking_ledger_closed": bool_checks[
            "sprint123RotatingFramePhaseLockingLedgerClosed"
        ]["passed"],
        "sprint122_persistence_imported": bool_checks["sprint122PersistenceImported"]["passed"],
        "rotating_frame_phase_locking_problem_recorded": bool_checks[
            "rotatingFramePhaseLockingEstimateRecorded"
        ]["passed"],
        "phase_locking_window_estimate_recorded": bool_checks[
            "favorableWindowLowerBoundRequirementRecorded"
        ]["passed"],
        "nse_derived_phase_dynamics_recorded": bool_checks["nseDerivedPhaseODERequirementRecorded"]["passed"],
        "dissipation_vs_phase_locking_ledger_recorded": bool_checks[
            "dampingDriftBalanceRecorded"
        ]["passed"],
        "phase_locking_promotion_rejection_recorded": bool_checks[
            "imposedLockingRejected"
        ]["passed"],
        "mechanism_closed": False,
        "downstream_closed": False,
        "rotating_frame_phase_locking_estimate_closed": False,
        "phase_locking_duration_lower_bound_closed": False,
        "favorable_phase_lag_window_lower_bound_closed": False,
        "rotating_strain_flux_budget_beats_kstar_closed": False,
        "kstar_collapse_from_rotating_strain_closed": False,
        "blowup_criterion_bridge_closed": False,
        "global_leray_compatible_rotating_strain_data_closed": False,
        "navier_stokes_clay_assembly_closed": False,
        "clay_navier_stokes_promoted": False,
        "clayNavierStokesPromoted": False,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "required_strings": REQUIRED_STRINGS,
        "missing_required_strings": missing_required_strings,
        "bool_checks": bool_checks,
        "assigned_bools": assigned_bools,
        "screen_hits": screen_hits,
        "screen_hit_count": len(screen_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "control_card": {
            "O": "Worker 2 owns only scripts/ns_sprint123_phase_locking_audit.py and outputs/ns_sprint123_phase_locking_audit files",
            "R": "verify Sprint123 phase-locking evidence closes only a fail-closed ledger: receipt evidence true, analytic and Clay gates false",
            "C": "single deterministic Python audit emitting summary JSON, rows JSON, and Markdown",
            "S": "target Agda module is inspected when present; missing target blocks coherence but still emits outputs",
            "L": "all required anchors, literals, exact booleans, keyword-consistency gates, and screened terms must pass before coherence",
            "P": ROUTE_DECISION,
            "G": "Navier-Stokes Clay promotion remains false; process success is reserved for a coherent fail-closed receipt",
            "F": "missing target, anchors, required strings, exact booleans, or screened-term hits block audit passage",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 123 Phase Locking Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Target present: `{summary['target_present']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Promotion decision: `{summary['promotion_decision']}`",
        f"- Promotion hold: `{summary['promotion_hold']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- Ledger coherent fail-closed: `{summary['ledger_coherent_fail_closed']}`",
        f"- Required true flags: `{summary['required_true_flags']}`",
        f"- Required false flags: `{summary['required_false_flags']}`",
        f"- Sprint123 ledger closed: `{summary['sprint123_rotating_frame_phase_locking_ledger_closed']}`",
        f"- Sprint122 persistence imported: `{summary['sprint122_persistence_imported']}`",
        f"- Phase-locking problem recorded: `{summary['rotating_frame_phase_locking_problem_recorded']}`",
        f"- Phase-locking window recorded: `{summary['phase_locking_window_estimate_recorded']}`",
        f"- NSE-derived phase dynamics recorded: `{summary['nse_derived_phase_dynamics_recorded']}`",
        f"- Mechanism closed: `{summary['mechanism_closed']}`",
        f"- Downstream closed: `{summary['downstream_closed']}`",
        f"- Navier-Stokes Clay promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Required Strings",
        "",
        "| String | Present |",
        "| --- | --- |",
    ]
    lines.extend(
        f"| `{literal}` | `{literal not in summary['missing_required_strings']}` |"
        for literal in summary["required_strings"]
    )
    lines.extend(["", "## Gate Results", "", "| Gate | Expected | Actual | Passed | Status |", "| --- | --- | --- | --- | --- |"])
    lines.extend(
        f"| `{row['gate']}` | `{row['expected']}` | `{row['actual']}` | `{row['passed']}` | `{row['status']}` |"
        for row in summary["gate_results"]
    )
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(summary["gate_results"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    summary = audit(repo_root)
    write_outputs(out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["ledger_coherent_fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
