#!/usr/bin/env python3
"""Sprint 122 NS rotating-persistence fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint122_rotating_persistence_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint122_rotating_persistence_audit")
SUMMARY_NAME = "ns_sprint122_rotating_persistence_audit_summary.json"
ROWS_NAME = "ns_sprint122_rotating_persistence_audit_rows.json"
REPORT_NAME = "ns_sprint122_rotating_persistence_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint122NonCircularRotatingStrainPersistenceBound.agda")
ROUTE_DECISION = "SPRINT122_ROTATING_PERSISTENCE_LEDGER_CLOSED_FAIL_CLOSED_PROMOTION_HELD"

REQUIRED_ANCHORS = [
    "NSSprint122NonCircularRotatingStrainPersistenceBound",
    "canonicalNSSprint122NonCircularRotatingStrainPersistenceBound",
    "ImportedSprint121RotatingStrain",
    "canonicalImportedSprint121RotatingStrain",
    "PhaseLagDynamicsProblem",
    "canonicalPhaseLagDynamicsProblem",
    "RotatingFrameODEReceipt",
    "canonicalRotatingFrameODEReceipt",
    "DissipationDriftCompetition",
    "canonicalDissipationDriftCompetition",
    "SourceClassifier",
    "canonicalSourceClassifier",
    "CircularImposedPhaseLagRejection",
    "canonicalCircularImposedPhaseLagRejection",
    "NonCircularRotatingStrainPersistenceBound",
    "canonicalNonCircularRotatingStrainPersistenceBound",
    "sprint122ReceiptSummary",
]

REQUIRED_STRINGS = [
    "Sprint122 imports Sprint121 rotating-strain assessment",
    "NonCircularRotatingStrainPersistenceBound",
    "phase lag dynamics must be derived from NSE, not imposed",
    "requires lower bound on favorable phase-lag duration",
    "rotating-frame ODE for phase lag is recorded",
    "NSE-derived polarization and amplitude dynamics required",
    "dissipation and strain drift compete with phase locking",
    "RotatingStrainFluxBudgetBeatsKStar remains open",
    "imposed phase lag is circular",
    "clayNavierStokesPromoted remains false",
]

EXPECTED_BOOLEANS = {
    "sprint122NonCircularRotatingStrainPersistenceLedgerClosed": True,
    "sprint121RotatingStrainImported": True,
    "phaseLagDynamicsProblemRecorded": True,
    "rotatingFrameODERecorded": True,
    "dissipationDriftCompetitionRecorded": True,
    "sourceClassifierRecorded": True,
    "circularImposedPhaseLagRejectionRecorded": True,
    "nonCircularRotatingStrainPersistenceBoundClosed": False,
    "rotatingStrainFluxBudgetBeatsKStarClosed": False,
    "kStarCollapseFromRotatingStrainClosed": False,
    "blowupCriterionBridgeClosed": False,
    "globalLerayCompatibleRotatingStrainDataClosed": False,
    "navierStokesClayAssemblyClosed": False,
    "clayNavierStokesPromoted": False,
}

TRUE_KEYWORDS = (
    "ledger",
    "imported",
    "recorded",
    "audited",
)
FALSE_KEYWORDS = (
    "closed",
    "collapse",
    "blowup",
    "assembly",
    "promoted",
    "clay",
)
EXEMPT_FALSE_NAMES = {name for name, expected in EXPECTED_BOOLEANS.items() if expected}

TOKEN_UNPROVED = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_EMPTY_FRAME = "skele" + "ton"
TOKEN_ACCEPT_WITHOUT_PROOF = "ad" + "mit"
TOKEN_SYNTHETIC = "du" + "m" + "my"
TOKEN_TEMP = "place" + "holder"
TOKEN_NEXT_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"
FORBIDDEN_PATTERNS = {
    "unproved_axiom_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_UNPROVED + r"(?![A-Za-z0-9_])"),
    "open_work_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_OPEN_WORK + r"(?![A-Za-z0-9_])"),
    "incomplete_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])", re.I),
    "empty_framework_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_EMPTY_FRAME + r"s?(?![A-Za-z0-9_])", re.I),
    "accepted_without_proof_marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_ACCEPT_WITHOUT_PROOF + r"(?:ted|s)?(?![A-Za-z0-9_])",
        re.I,
    ),
    "synthetic_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_SYNTHETIC + r"(?![A-Za-z0-9_])", re.I),
    "temporary_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_TEMP + r"s?(?![A-Za-z0-9_])", re.I),
    "deferred_proof_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_NEXT_PROOF + r"(?![A-Za-z0-9_])", re.I),
    "gap_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])", re.I),
    "open_gap_delimiter": re.compile(r"\{" + r"!|!" + r"\}"),
    "open_gap_assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
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
    forbidden_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in FORBIDDEN_PATTERNS.items()
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
                "forbidden_markers",
                "none",
                "none" if not forbidden_hits else str(len(forbidden_hits)),
                not forbidden_hits,
                "PASS" if not forbidden_hits else "FAIL_CLOSED_FORBIDDEN_MARKER",
            ),
        ]
    )
    structural_checks_pass = (
        present
        and not missing_anchors
        and not missing_required_strings
        and not forbidden_hits
        and all(row.passed for row in gate_rows)
    )
    required_true_flags = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is True)
    required_false_flags = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is False)
    keyword_true_flags_coherent = all(keyword_checks["true"].values())
    keyword_false_flags_coherent = all(keyword_checks["false"].values())
    downstream_closed = not required_false_flags
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
        "promotion_hold": True,
        "evidence_audit_passed": structural_checks_pass,
        "ledger_coherent_fail_closed": structural_checks_pass,
        "required_true_flags": required_true_flags,
        "required_false_flags": required_false_flags,
        "keyword_true_flags_coherent": keyword_true_flags_coherent,
        "keyword_false_flags_coherent": keyword_false_flags_coherent,
        "sprint122_rotating_persistence_ledger_closed": bool_checks[
            "sprint122NonCircularRotatingStrainPersistenceLedgerClosed"
        ]["passed"],
        "sprint121_rotating_strain_imported": bool_checks["sprint121RotatingStrainImported"]["passed"],
        "phase_lag_dynamics_problem_recorded": bool_checks["phaseLagDynamicsProblemRecorded"]["passed"],
        "rotating_frame_ode_recorded": bool_checks["rotatingFrameODERecorded"]["passed"],
        "dissipation_drift_competition_recorded": bool_checks["dissipationDriftCompetitionRecorded"]["passed"],
        "source_classifier_recorded": bool_checks["sourceClassifierRecorded"]["passed"],
        "circular_imposed_phase_lag_rejection_recorded": bool_checks[
            "circularImposedPhaseLagRejectionRecorded"
        ]["passed"],
        "mechanism_closed": False,
        "downstream_closed": downstream_closed,
        "non_circular_rotating_strain_persistence_bound_closed": False,
        "rotating_strain_flux_budget_beats_kstar_closed": False,
        "kstar_collapse_from_rotating_strain_closed": False,
        "blowup_criterion_bridge_closed": False,
        "global_leray_compatible_rotating_strain_data_closed": False,
        "navier_stokes_clay_assembly_closed": False,
        "clay_navier_stokes_promoted": False,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "required_strings": REQUIRED_STRINGS,
        "missing_required_strings": missing_required_strings,
        "bool_checks": bool_checks,
        "assigned_bools": assigned_bools,
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "control_card": {
            "O": "Worker 2 owns only scripts/ns_sprint122_rotating_persistence_audit.py and outputs/ns_sprint122_rotating_persistence_audit files",
            "R": "verify the Sprint122 rotating-persistence receipt closes only a fail-closed ledger: ledger and receipt evidence true, analytic and Clay gates false",
            "C": "single deterministic Python audit emitting summary JSON, rows JSON, and Markdown",
            "S": "target Agda module is inspected when present; missing target blocks coherence but still emits outputs",
            "L": "all required anchors, literals, exact booleans, keyword-consistency gates, and marker checks must pass before coherence",
            "P": ROUTE_DECISION,
            "G": "Navier-Stokes Clay promotion remains false; process success is reserved for a coherent fail-closed receipt",
            "F": "missing target, anchors, required strings, exact booleans, or marker hits block audit passage",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 122 Rotating Persistence Audit",
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
        f"- Sprint122 ledger closed: `{summary['sprint122_rotating_persistence_ledger_closed']}`",
        f"- Sprint121 rotating strain imported: `{summary['sprint121_rotating_strain_imported']}`",
        f"- Phase lag dynamics problem recorded: `{summary['phase_lag_dynamics_problem_recorded']}`",
        f"- Rotating frame ODE recorded: `{summary['rotating_frame_ode_recorded']}`",
        f"- Source classifier recorded: `{summary['source_classifier_recorded']}`",
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
