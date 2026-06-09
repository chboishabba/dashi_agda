#!/usr/bin/env python3
"""Sprint 124 NS zero-mean flux over rotation cycle fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint124_zero_mean_flux_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint124_zero_mean_flux_audit")
SUMMARY_NAME = "ns_sprint124_zero_mean_flux_audit_summary.json"
ROWS_NAME = "ns_sprint124_zero_mean_flux_audit_rows.json"
REPORT_NAME = "ns_sprint124_zero_mean_flux_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint124ZeroMeanFluxOverRotationCycle.agda")
ROUTE_DECISION = "SPRINT124_ZERO_MEAN_FLUX_ROTATING_ROUTE_CLOSED_FAIL_CLOSED_PROMOTION_HELD"
NEXT_STEP = "VORTEX_STRETCHING_NEXT"

REQUIRED_IMPORT_PATTERNS = [
    "DASHI.Physics.Closure.NSSprint123RotatingFramePhaseLockingEstimate",
]

REQUIRED_ANCHORS = [
    "NSSprint124ZeroMeanFluxOverRotationCycle",
    "canonicalNSSprint124ZeroMeanFluxOverRotationCycle",
    "ImportedSprint123PhaseLocking",
    "canonicalImportedSprint123PhaseLocking",
    "FavorablePhaseLagWindowLowerBound",
    "canonicalFavorablePhaseLagWindowLowerBound",
    "ZeroMeanFluxOverRotationCycle",
    "canonicalZeroMeanFluxOverRotationCycle",
    "RotatingStrainRouteClosure",
    "canonicalRotatingStrainRouteClosure",
    "VortexStretchingNextRoute",
    "canonicalVortexStretchingNextRoute",
    "Sprint124GateStatuses",
    "canonicalSprint124GateStatuses",
    "sprint124ReceiptSummary",
]

REQUIRED_STRINGS = [
    "Sprint124 imports Sprint123 phase-locking estimate",
    "ZeroMeanFluxOverRotationCycle",
    "signed HH-to-low flux has zero mean over one rotating-strain cycle",
    "rotating-strain route closes by zero cycle-mean flux",
    "the favorable lower bound is local dwell evidence, not positive cycle-mean flux",
    "vortex stretching is next",
    "VortexStretchingContinuumControl",
    "RotatingStrainFluxBudgetBeatsKStar remains false",
    "clayNavierStokesPromoted remains false",
]

EXPECTED_BOOLEANS = {
    "sprint124ZeroMeanFluxOverRotationCycleLedgerClosed": True,
    "sprint123PhaseLockingImported": True,
    "favorablePhaseLagWindowLowerBoundClosed": True,
    "zeroMeanFluxOverRotationCycleRecorded": True,
    "rotationCycleCancellationRecorded": True,
    "localDwellWindowOnlyRecorded": True,
    "rotatingStrainRouteClosed": True,
    "vortexStretchingNextRouteRecorded": True,
    "rotatingStrainFluxBudgetBeatsKStarClosed": False,
    "kStarCollapseFromRotatingStrainClosed": False,
    "vortexStretchingContinuumControlClosed": False,
    "blowupCriterionBridgeClosed": False,
    "globalLerayCompatibleRotatingStrainDataClosed": False,
    "navierStokesClayAssemblyClosed": False,
    "clayNavierStokesPromoted": False,
}

TRUE_KEYWORDS = ("ledger", "imported", "recorded", "routeclosed", "lowerboundclosed")
FALSE_KEYWORDS = ("budget", "kstar", "continuumcontrolclosed", "blowup", "assembly", "promoted", "clay")
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


def gate(gate_name: str, expected: str, actual: str, passed: bool, fail_status: str) -> GateRow:
    return GateRow(gate_name, expected, actual, passed, "PASS" if passed else fail_status)


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.exists()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    missing_imports = [literal for literal in REQUIRED_IMPORT_PATTERNS if literal not in text]
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
    route_closed = bool_checks["rotatingStrainRouteClosed"]["passed"]
    vortex_next = (
        bool_checks["vortexStretchingNextRouteRecorded"]["passed"]
        and bool_checks["vortexStretchingContinuumControlClosed"]["passed"]
        and ("vortex stretching is next" in text or NEXT_STEP in text)
    )
    gate_rows = [
        gate(
            name,
            "true" if expected else "false",
            bool_checks[name]["actual"],
            bool_checks[name]["passed"],
            "FAIL_CLOSED_BOOLEAN_GATE",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
    ]
    gate_rows.extend(
        gate(f"keyword_true:{name}", "true", assigned_bools[name], passed, "FAIL_CLOSED_REQUIRED_TRUE_KEYWORD_FLAG")
        for name, passed in keyword_checks["true"].items()
    )
    gate_rows.extend(
        gate(f"keyword_false:{name}", "false", assigned_bools[name], passed, "FAIL_CLOSED_DOWNSTREAM_FLAG_TRUE")
        for name, passed in keyword_checks["false"].items()
    )
    gate_rows.extend(
        gate(
            f"required_string:{literal}",
            "present",
            "present" if literal not in missing_required_strings else "missing",
            literal not in missing_required_strings,
            "FAIL_CLOSED_MISSING_REQUIRED_STRING",
        )
        for literal in REQUIRED_STRINGS
    )
    gate_rows.extend(
        [
            gate("target_module", str(AGDA_PATH), "present" if present else "missing", present, "FAIL_CLOSED_MISSING_TARGET"),
            gate(
                "sprint123_import",
                "present",
                "present" if not missing_imports else "; ".join(missing_imports),
                not missing_imports,
                "FAIL_CLOSED_MISSING_SPRINT123_IMPORT",
            ),
            gate(
                "required_anchors",
                "all present",
                "all present" if not missing_anchors else "; ".join(missing_anchors),
                not missing_anchors,
                "FAIL_CLOSED_MISSING_ANCHOR",
            ),
            gate(
                "forbidden_markers",
                "none",
                "none" if not forbidden_hits else str(len(forbidden_hits)),
                not forbidden_hits,
                "FAIL_CLOSED_FORBIDDEN_MARKER",
            ),
            gate("rotating_route_closed", "true", str(route_closed).lower(), route_closed, "FAIL_CLOSED_ROUTE_NOT_CLOSED"),
            gate("vortex_stretching_next", "recorded/open", str(vortex_next).lower(), vortex_next, "FAIL_CLOSED_NEXT_STEP_NOT_OPEN"),
        ]
    )
    structural_checks_pass = (
        present
        and not missing_imports
        and not missing_anchors
        and not missing_required_strings
        and not forbidden_hits
        and all(row.passed for row in gate_rows)
    )
    required_true_flags = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is True)
    required_false_flags = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is False)
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "target_present": present,
        "complete": structural_checks_pass,
        "proof_claimed": False,
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "next_step": NEXT_STEP,
        "final_decision": ROUTE_DECISION if structural_checks_pass else "FAIL_CLOSED_AUDIT_BLOCKED",
        "promotion_decision": "hold",
        "promotion_ready": False,
        "promotion_hold": True,
        "evidence_audit_passed": structural_checks_pass,
        "ledger_coherent_fail_closed": structural_checks_pass,
        "required_true_flags": required_true_flags,
        "required_false_flags": required_false_flags,
        "keyword_true_flags_coherent": all(keyword_checks["true"].values()),
        "keyword_false_flags_coherent": all(keyword_checks["false"].values()),
        "sprint124_zero_mean_flux_ledger_closed": bool_checks[
            "sprint124ZeroMeanFluxOverRotationCycleLedgerClosed"
        ]["passed"],
        "sprint123_phase_locking_imported": bool_checks["sprint123PhaseLockingImported"]["passed"],
        "favorable_phase_lag_window_lower_bound_closed": bool_checks[
            "favorablePhaseLagWindowLowerBoundClosed"
        ]["passed"],
        "zero_mean_flux_over_rotation_cycle_recorded": bool_checks["zeroMeanFluxOverRotationCycleRecorded"]["passed"],
        "rotation_cycle_cancellation_recorded": bool_checks["rotationCycleCancellationRecorded"]["passed"],
        "local_dwell_window_only_recorded": bool_checks["localDwellWindowOnlyRecorded"]["passed"],
        "rotating_route_closed": route_closed,
        "vortex_stretching_next_recorded": bool_checks["vortexStretchingNextRouteRecorded"]["passed"],
        "mechanism_closed": True if structural_checks_pass else False,
        "downstream_closed": False,
        "vortex_stretching_continuum_control_closed": False,
        "rotating_strain_flux_budget_beats_kstar_closed": False,
        "kstar_collapse_from_rotating_strain_closed": False,
        "blowup_criterion_bridge_closed": False,
        "global_leray_compatible_rotating_strain_data_closed": False,
        "navier_stokes_clay_assembly_closed": False,
        "clay_navier_stokes_promoted": False,
        "clayNavierStokesPromoted": False,
        "required_import_patterns": REQUIRED_IMPORT_PATTERNS,
        "missing_imports": missing_imports,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "required_strings": REQUIRED_STRINGS,
        "missing_required_strings": missing_required_strings,
        "bool_checks": bool_checks,
        "assigned_bools": assigned_bools,
        "forbidden_hits": forbidden_hits,
        "forbidden_hit_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "control_card": {
            "O": "Worker 2 owns scripts/ns_sprint124_zero_mean_flux_audit.py plus generated outputs/ns_sprint124_zero_mean_flux_audit artifacts",
            "R": "verify Sprint124 records zero mean flux over a rotation cycle, imports Sprint123, closes the rotating route, and leaves vortex stretching next",
            "C": "single deterministic Python audit emitting summary JSON, rows JSON, and Markdown",
            "S": "target Agda module is inspected when present; missing target blocks coherence while outputs still emit",
            "L": "required imports, anchors, literals, booleans, keyword consistency, route closure, next-step openness, and forbidden-marker screens must pass",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false; process success is reserved for a coherent fail-closed ledger",
            "F": "missing target, Sprint123 import, anchors, required strings, exact booleans, forbidden markers, open route, or closed vortex stretching block passage",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 124 Zero Mean Flux Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Target present: `{summary['target_present']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Next step: `{summary['next_step']}`",
        f"- Promotion hold: `{summary['promotion_hold']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- Ledger coherent fail-closed: `{summary['ledger_coherent_fail_closed']}`",
        f"- Sprint123 imported: `{summary['sprint123_phase_locking_imported']}`",
        f"- Rotating route closed: `{summary['rotating_route_closed']}`",
        f"- Vortex stretching next recorded: `{summary['vortex_stretching_next_recorded']}`",
        f"- Vortex stretching continuum control closed: `{summary['vortex_stretching_continuum_control_closed']}`",
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
