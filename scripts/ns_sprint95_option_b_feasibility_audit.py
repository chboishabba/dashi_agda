#!/usr/bin/env python3
"""Sprint 95 NS Option B blowup feasibility audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint95_option_b_feasibility_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint95_option_b_feasibility_audit")
SUMMARY_NAME = "ns_sprint95_option_b_feasibility_audit_summary.json"
ROWS_NAME = "ns_sprint95_option_b_feasibility_audit_rows.json"
GATE_CSV_NAME = "ns_sprint95_option_b_feasibility_gate_table.csv"
SOURCE_CSV_NAME = "ns_sprint95_option_b_feasibility_source_table.csv"
REPORT_NAME = "ns_sprint95_option_b_feasibility_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint95OptionBBlowupFeasibilityLedger.agda")

REQUIRED_ANCHORS = [
    "canonicalNSSprint95OptionBBlowupFeasibilityLedger",
    "KStarCollapseHypothesis",
    "FiniteTimeBlowupMechanism",
    "LowFrequencyCascadeCandidate",
    "SmoothFiniteEnergyInitialDataCompatibility",
    "OptionBBlowupFeasibilityGate",
    "kStarCollapseMechanism",
    "compatibilityWithLerayEnergy",
    "exclusionOfConditionalKStarLowerBound",
    "finiteTimeSingularityExtraction",
]

EXPECTED_BOOLEANS = {
    "optionBBlowupFeasibilityLedgerClosed": True,
    "optionBFeasibilityLedgerClosed": True,
    "blowupConstructionClosed": False,
    "optionBBlowupConstructionClosed": False,
    "kStarCollapseMechanismClosed": False,
    "compatibilityWithLerayEnergyClosed": False,
    "exclusionOfConditionalKStarLowerBoundClosed": False,
    "finiteTimeSingularityExtractionClosed": False,
    "clayNavierStokesPromoted": False,
}

INHERITED_SPRINT94_TRUE = {
    "sprint94ObstructionInherited": (
        "sprint94ObstructionInherited",
        "Sprint94.generalDataGateObstructedByKStarLowerBound",
    ),
    "sprint94ConditionalKStarInherited": (
        "sprint94ConditionalCriterionInherited",
        "Sprint94.optionCConditionalRegularityCriterionClosed",
    ),
}

OPEN_GATE_NAMES = (
    "kStarCollapseMechanismClosed",
    "compatibilityWithLerayEnergyClosed",
    "exclusionOfConditionalKStarLowerBoundClosed",
    "finiteTimeSingularityExtractionClosed",
)

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "todo": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.I),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admit(?:ted|s)?(?![A-Za-z0-9_])", re.I),
    "agda_hole_start": re.compile(r"\{!"),
    "agda_hole_end": re.compile(r"!\}"),
}


@dataclass(frozen=True)
class GateRow:
    gate: str
    expected: str
    actual: str
    passed: bool
    status: str


@dataclass(frozen=True)
class SourceRow:
    source: str
    present: bool
    missing_anchors: str
    status: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def bool_assignment(text: str, name: str, expected: bool) -> bool:
    value = "true" if expected else "false"
    pattern = re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(name)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + value
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )
    return bool(pattern.search(text))


def actual_bool_assignment(text: str, name: str) -> str:
    if bool_assignment(text, name, True):
        return "true"
    if bool_assignment(text, name, False):
        return "false"
    return "missing"


def inherited_true_proof(text: str, field_name: str, sprint94_flag: str) -> bool:
    field_pattern = re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(field_name)
        + r"(?![A-Za-z0-9_])\s*:\s*"
        + re.escape(sprint94_flag)
        + r"\s*≡\s*true",
        re.MULTILINE,
    )
    refl_pattern = re.compile(r";\s*" + re.escape(field_name) + r"\s*=\s*refl\b")
    return bool(field_pattern.search(text) and refl_pattern.search(text))


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.exists()
    text = path.read_text(encoding="utf-8") if present else ""
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if anchor not in text]
    bool_checks = {
        name: {
            "expected": expected,
            "actual": actual_bool_assignment(text, name),
            "passed": bool_assignment(text, name, expected),
        }
        for name, expected in EXPECTED_BOOLEANS.items()
    }
    inherited_checks = {
        name: {
            "expected": True,
            "actual": "true" if passed else "missing",
            "passed": passed,
        }
        for name, (field_name, flag) in INHERITED_SPRINT94_TRUE.items()
        for passed in [inherited_true_proof(text, field_name, flag)]
    }
    forbidden_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]
    gates = [
        GateRow(
            name,
            "true" if expected else "false",
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
        for data in [bool_checks[name]]
    ]
    gates.extend(
        GateRow(
            name,
            "true",
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL",
        )
        for name, data in inherited_checks.items()
    )
    source_rows = [
        SourceRow(
            str(AGDA_PATH),
            present,
            "none" if not missing_anchors else "; ".join(missing_anchors),
            "PASS" if present and not missing_anchors else "FAIL",
        )
    ]
    four_open_gates_false = all(bool_checks[name]["passed"] for name in OPEN_GATE_NAMES)
    inherited_sprint94_true = all(item["passed"] for item in inherited_checks.values())
    fail_closed = (
        present
        and not missing_anchors
        and not forbidden_hits
        and all(item["passed"] for item in bool_checks.values())
        and inherited_sprint94_true
    )
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "complete": False,
        "fail_closed": fail_closed,
        "route_decision": "FAIL_CLOSED" if fail_closed else "AUDIT_FAILED",
        "final_decision": "FAIL_CLOSED_OPTION_B_FEASIBILITY" if fail_closed else "AUDIT_FAILED",
        "promotion_decision": "hold",
        "optionBFeasibilityLedgerClosed": bool_checks["optionBFeasibilityLedgerClosed"]["passed"],
        "option_b_feasibility_ledger_closed": bool_checks["optionBBlowupFeasibilityLedgerClosed"]["passed"],
        "blowup_construction_closed": False if bool_checks["blowupConstructionClosed"]["passed"] else None,
        "option_b_blowup_construction_closed": False if bool_checks["optionBBlowupConstructionClosed"]["passed"] else None,
        "kstar_collapse_mechanism_closed": False if bool_checks["kStarCollapseMechanismClosed"]["passed"] else None,
        "compatibility_with_leray_energy_closed": False if bool_checks["compatibilityWithLerayEnergyClosed"]["passed"] else None,
        "exclusion_of_conditional_kstar_lower_bound_closed": False if bool_checks["exclusionOfConditionalKStarLowerBoundClosed"]["passed"] else None,
        "finite_time_singularity_extraction_closed": False if bool_checks["finiteTimeSingularityExtractionClosed"]["passed"] else None,
        "four_open_gates_false": four_open_gates_false,
        "open_gate_names": list(OPEN_GATE_NAMES),
        "inherited_sprint94_conditional_obstruction_true": inherited_sprint94_true,
        "sprint94_inherited": inherited_sprint94_true,
        "sprint94_obstruction_inherited": inherited_checks["sprint94ObstructionInherited"]["passed"],
        "sprint94_conditional_kstar_inherited": inherited_checks["sprint94ConditionalKStarInherited"]["passed"],
        "conditional_criterion": False,
        "general_data": False,
        "clay_navier_stokes_promoted": False if bool_checks["clayNavierStokesPromoted"]["passed"] else None,
        "required_residual_gate": "finite-time K* collapse mechanism",
        "missing_anchors": missing_anchors,
        "forbidden_hits": forbidden_hits,
        "forbidden_term_count": len(forbidden_hits),
        "bool_checks": bool_checks,
        "inherited_checks": inherited_checks,
        "gate_results": [asdict(row) for row in gates],
        "source_results": [asdict(row) for row in source_rows],
        "surface": "NSSprint95 Sprint95 OptionB Feasibility fail_closed Clay blowup Sprint94",
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = {"gates": summary["gate_results"], "sources": summary["source_results"]}
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(out_dir / GATE_CSV_NAME, rows["gates"])
    write_csv(out_dir / SOURCE_CSV_NAME, rows["sources"])
    lines = [
        "# NS Sprint 95 Option B Feasibility Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Surface: `{summary['surface']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- Option B feasibility ledger closed: `{summary['option_b_feasibility_ledger_closed']}`",
        f"- optionBFeasibilityLedgerClosed: `{summary['optionBFeasibilityLedgerClosed']}`",
        f"- Sprint94 inherited: `{summary['sprint94_inherited']}`",
        f"- Conditional-criterion exclusion gate closed: `{summary['conditional_criterion']}`",
        f"- General data Clay route closed: `False`",
        f"- Blowup construction closed: `{summary['blowup_construction_closed']}`",
        f"- Option B blowup construction closed: `{summary['option_b_blowup_construction_closed']}`",
        f"- K-star collapse mechanism closed: `{summary['kstar_collapse_mechanism_closed']}`",
        f"- Compatibility with Leray energy closed: `{summary['compatibility_with_leray_energy_closed']}`",
        f"- Exclusion of conditional K-star lower bound closed: `{summary['exclusion_of_conditional_kstar_lower_bound_closed']}`",
        f"- Finite-time singularity extraction closed: `{summary['finite_time_singularity_extraction_closed']}`",
        f"- Four open gates false: `{summary['four_open_gates_false']}`",
        f"- Sprint94 conditional/obstruction inherited true: `{summary['inherited_sprint94_conditional_obstruction_true']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Required residual gate: `{summary['required_residual_gate']}`",
    ]
    (out_dir / REPORT_NAME).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root)
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
