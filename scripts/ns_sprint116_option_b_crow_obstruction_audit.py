#!/usr/bin/env python3
"""Sprint 116 NS Option B Crow obstruction fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint116_option_b_crow_obstruction_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint116_option_b_crow_obstruction_audit")
SUMMARY_NAME = "ns_sprint116_option_b_crow_obstruction_audit_summary.json"
ROWS_NAME = "ns_sprint116_option_b_crow_obstruction_audit_rows.json"
REPORT_NAME = "ns_sprint116_option_b_crow_obstruction_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint116OptionBCrowObstruction.agda")
ROUTE_DECISION = "OPTION_B_CROW_OBSTRUCTION_LEDGER_CLOSED_FAIL_CLOSED_ALTERNATIVE_ROUTE_OPEN"

REQUIRED_ANCHORS = [
    "NSSprint116OptionBCrowObstruction",
    "canonicalNSSprint116OptionBCrowObstruction",
    "nsSprint116OptionBCrowObstructionReceipt",
    "canonicalNSSprint116OptionBCrowObstructionReceipt",
    "canonicalOptionBCrowObstructionReceipt",
    "ImportedSprint115FluxBudget",
    "canonicalImportedSprint115FluxBudget",
    "ThinCoreCrowScalingObstruction",
    "canonicalThinCoreCrowScalingObstruction",
    "AlternateRouteStatus",
    "canonicalAlternateRouteStatus",
    "Sprint116GateStatuses",
    "canonicalSprint116GateStatuses",
    "canonicalSprint116OptionBCrowObstructionFlags",
]

REQUIRED_STRINGS = [
    "Sprint 116 Option B thin-core Crow obstruction.",
    "This receipt imports the Sprint115 reconnection flux budget and records",
    "that the thin-core Crow Option B lane is closed by the budget scaling.",
    "FluxBudget / E0 ~ (delta / b)^2 / log(b / delta)",
    "Option B thin-core Crow route is obstructed",
    "axisymmetric with swirl remains open",
    "Burgers vortex concentration remains open",
    "Sprint116 records the Option B obstruction without closing finite KStar collapse, the blowup bridge, or the Clay assembly.",
]

EXPECTED_BOOLEANS = {
    "sprint116OptionBCrowObstructionLedgerClosed": True,
    "sprint115FluxBudgetImported": True,
    "thinCoreCrowScalingLawRecorded": True,
    "thinCoreCrowRouteObstructed": True,
    "optionBCrowLaneClosed": True,
    "axisymmetricSwirlRouteOpen": True,
    "burgersVortexRouteOpen": True,
    "finiteKStarCollapseClosed": False,
    "blowupCriterionBridgeClosed": False,
    "navierStokesClayAssemblyClosed": False,
    "clayNavierStokesPromoted": False,
}

TRUE_KEYWORDS = (
    "ledger",
    "import",
    "scaling",
    "obstruct",
    "laneclosed",
    "routeopen",
)
FALSE_KEYWORDS = (
    "finitekstar",
    "blowup",
    "assembly",
    "clay",
)
EXEMPT_FALSE_NAMES = {name for name, expected in EXPECTED_BOOLEANS.items() if expected}

TOKEN_UNPROVED = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_EMPTY_FRAME = "skele" + "ton"
TOKEN_ACCEPT_WITHOUT_PROOF = "ad" + "mit"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"
FORBIDDEN_PATTERNS = {
    "unproved_axiom_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_UNPROVED + r"(?![A-Za-z0-9_])"),
    "open_work_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_OPEN_WORK + r"(?![A-Za-z0-9_])"),
    "incomplete_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])", re.I),
    "empty_framework_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_EMPTY_FRAME + r"s?(?![A-Za-z0-9_])", re.I),
    "accepted_without_proof_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_ACCEPT_WITHOUT_PROOF + r"(?:ted|s)?(?![A-Za-z0-9_])", re.I),
    "synthetic_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])", re.I),
    "deferred_proof_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])", re.I),
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
    downstream_flags_false = all(check["passed"] for name, check in bool_checks.items() if EXPECTED_BOOLEANS[name] is False)
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
        "promotion_hold": True,
        "evidence_audit_passed": structural_checks_pass,
        "ledger_coherent_fail_closed": structural_checks_pass,
        "required_true_flags": required_true_flags,
        "downstream_flags_false": downstream_flags_false,
        "keyword_true_flags_coherent": keyword_true_flags_coherent,
        "keyword_false_flags_coherent": keyword_false_flags_coherent,
        "sprint116_option_b_crow_obstruction_ledger_closed": bool_checks[
            "sprint116OptionBCrowObstructionLedgerClosed"
        ]["passed"],
        "sprint115_flux_budget_imported": bool_checks["sprint115FluxBudgetImported"]["passed"],
        "sprint115_reconnection_flux_budget_imported": bool_checks["sprint115FluxBudgetImported"]["passed"],
        "thin_core_crow_scaling_law_recorded": bool_checks["thinCoreCrowScalingLawRecorded"]["passed"],
        "crow_scaling_obstruction_recorded": bool_checks["thinCoreCrowScalingLawRecorded"]["passed"],
        "thin_core_crow_route_obstructed": bool_checks["thinCoreCrowRouteObstructed"]["passed"],
        "option_b_crow_obstructed": bool_checks["thinCoreCrowRouteObstructed"]["passed"],
        "option_b_crow_lane_closed": bool_checks["optionBCrowLaneClosed"]["passed"],
        "option_b_lane_closed": bool_checks["optionBCrowLaneClosed"]["passed"],
        "axisymmetric_swirl_route_open": bool_checks["axisymmetricSwirlRouteOpen"]["passed"],
        "burgers_vortex_route_open": bool_checks["burgersVortexRouteOpen"]["passed"],
        "alternative_route_open": bool_checks["axisymmetricSwirlRouteOpen"]["passed"]
        and bool_checks["burgersVortexRouteOpen"]["passed"],
        "finite_kstar_collapse": False,
        "blowup_criterion_bridge": False,
        "navier_stokes_clay_assembly": False,
        "blowup_assembly": False,
        "clay": False,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "required_strings": REQUIRED_STRINGS,
        "missing_required_strings": missing_required_strings,
        "bool_checks": bool_checks,
        "assigned_bools": assigned_bools,
        "keyword_flag_checks": keyword_checks,
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "control_card": {
            "O": "Worker 2 owns the Sprint116 Option B Crow obstruction audit script only",
            "R": "verify the Sprint116 Agda ledger closes ledger/import/scaling/obstruction/lane/alternative-route evidence while keeping finite KStar, blowup, assembly, and Clay gates false",
            "C": "single deterministic Python audit emitting summary JSON, rows JSON, and Markdown",
            "S": "target Agda module is inspected when present; missing target fails closed",
            "L": "all required anchors, literals, exact booleans, and keyword-consistency gates must match before coherent passage",
            "P": ROUTE_DECISION,
            "G": "Clay promotion remains false; this audit succeeds only for a coherent fail-closed obstruction ledger",
            "F": "missing target, anchors, required strings, exact booleans, or forbidden-marker hits block audit passage",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 116 Option B Crow Obstruction Audit",
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
        f"- Downstream flags false: `{summary['downstream_flags_false']}`",
        f"- Sprint116 Option B Crow obstruction ledger closed: `{summary['sprint116_option_b_crow_obstruction_ledger_closed']}`",
        f"- Sprint115 flux budget imported: `{summary['sprint115_flux_budget_imported']}`",
        f"- Thin-core Crow scaling law recorded: `{summary['thin_core_crow_scaling_law_recorded']}`",
        f"- Thin-core Crow route obstructed: `{summary['thin_core_crow_route_obstructed']}`",
        f"- Option B Crow lane closed: `{summary['option_b_crow_lane_closed']}`",
        f"- Axisymmetric swirl route open: `{summary['axisymmetric_swirl_route_open']}`",
        f"- Burgers vortex route open: `{summary['burgers_vortex_route_open']}`",
        f"- Clay promoted: `{summary['clay']}`",
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
    summary = audit(args.repo_root.resolve())
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["ledger_coherent_fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
