#!/usr/bin/env python3
"""Sprint 96 NS K-star collapse mechanism constraints audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint96_kstar_collapse_constraints_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint96_kstar_collapse_constraints_audit")
SUMMARY_NAME = "ns_sprint96_kstar_collapse_constraints_audit_summary.json"
ROWS_NAME = "ns_sprint96_kstar_collapse_constraints_audit_rows.json"
GATE_CSV_NAME = "ns_sprint96_kstar_collapse_constraints_gate_table.csv"
SOURCE_CSV_NAME = "ns_sprint96_kstar_collapse_constraints_source_table.csv"
REPORT_NAME = "ns_sprint96_kstar_collapse_constraints_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint96KStarCollapseMechanismConstraints.agda")

REQUIRED_ANCHORS = [
    "NSSprint96KStarCollapseMechanismConstraints",
    "canonicalNSSprint96KStarCollapseMechanismConstraints",
    "KStarCollapseMechanismConstraints",
    "KStarCollapseMechanismResiduals",
    "kStarCollapseMechanismClosed",
    "clayNavierStokesPromoted",
    "failClosedKStarCollapseConstraints",
    "FAIL_CLOSED_KSTAR_COLLAPSE_CONSTRAINTS",
]

EXPECTED_BOOLEANS = {
    "kStarCollapseConstraintLedgerClosed": True,
    "kStarCollapseMechanismClosed": False,
    "optionBFiniteTimeKStarCollapseClosed": False,
    "lowModeEnergyConcentrationMechanism": False,
    "viscousDampingOvercomeMechanism": False,
    "scalingCompatibleSelfSimilarity": False,
    "singularityExtractionWithoutCriterionFailure": False,
    "clayNavierStokesPromoted": False,
}

REQUIRED_RESIDUALS = [
    "finite-time K-star collapse mechanism",
    "compatibility with Leray energy",
    "exclusion of conditional K-star lower bound",
    "finite-time singularity extraction",
]

RESIDUAL_ALIASES = {
    "finite-time K-star collapse mechanism": [
        "FiniteTimeKStarCollapseMechanismCandidate",
        "optionBFiniteTimeKStarCollapseClosed",
    ],
    "compatibility with Leray energy": [
        "ViscousDampingCompatibility",
        "compatibleWithSprint95LerayGate",
        "Sprint95.compatibilityWithLerayEnergyClosed",
    ],
    "exclusion of conditional K-star lower bound": [
        "avoidsSprint94CriterionFailure",
        "singularityExtractionWithoutCriterionFailure",
        "conditional-criterion boundary",
    ],
    "finite-time singularity extraction": [
        "SingularityExtractionBridge",
        "Sprint95.finiteTimeSingularityExtractionClosed",
        "singularityExtractionWithoutCriterionFailure",
    ],
}

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "todo": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.I),
    "placeholder": re.compile(r"(?<![A-Za-z0-9_])placeholder(?![A-Za-z0-9_])", re.I),
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


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def residual_present(text: str, residual: str) -> bool:
    compact = re.sub(r"[^A-Za-z0-9]+", "", residual).lower()
    surface = re.sub(r"[^A-Za-z0-9]+", "", text).lower()
    camel = residual.title().replace(" ", "").replace("-", "")
    return (
        residual in text
        or compact in surface
        or camel in text
        or any(alias in text for alias in RESIDUAL_ALIASES[residual])
    )


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
    residual_checks = {
        residual: {
            "expected": True,
            "actual": "present" if residual_present(text, residual) else "missing",
            "passed": residual_present(text, residual),
        }
        for residual in REQUIRED_RESIDUALS
    }
    forbidden_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]

    gate_rows = [
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
    gate_rows.extend(
        GateRow(
            residual,
            "present",
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL",
        )
        for residual, data in residual_checks.items()
    )
    source_rows = [
        SourceRow(
            str(AGDA_PATH),
            present,
            "none" if not missing_anchors else "; ".join(missing_anchors),
            "PASS" if present and not missing_anchors else "FAIL",
        )
    ]

    evidence_audit_passed = (
        present
        and not missing_anchors
        and not forbidden_hits
        and all(item["passed"] for item in bool_checks.values())
        and all(item["passed"] for item in residual_checks.values())
    )
    residuals_open = [residual for residual, data in residual_checks.items() if data["passed"]]

    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "complete": False,
        "fail_closed": True,
        "route_decision": "FAIL_CLOSED_KSTAR_COLLAPSE_CONSTRAINTS",
        "final_decision": "FAIL_CLOSED_KSTAR_COLLAPSE_CONSTRAINTS",
        "promotion_decision": "hold",
        "evidence_audit_passed": evidence_audit_passed,
        "clay_navier_stokes_promoted": False if bool_checks["clayNavierStokesPromoted"]["passed"] else None,
        "kstar_collapse_mechanism_closed": False
        if bool_checks["kStarCollapseMechanismClosed"]["passed"]
        else None,
        "sprint96_kstar_collapse_mechanism_constraints_closed": bool_checks[
            "kStarCollapseConstraintLedgerClosed"
        ]["passed"],
        "kstar_collapse_mechanism_constraints_closed": bool_checks[
            "kStarCollapseConstraintLedgerClosed"
        ]["passed"],
        "required_residuals": REQUIRED_RESIDUALS,
        "required_residuals_present": residuals_open,
        "required_residual_count": len(REQUIRED_RESIDUALS),
        "required_residuals_present_count": len(residuals_open),
        "missing_required_residuals": [
            residual for residual, data in residual_checks.items() if not data["passed"]
        ],
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "forbidden_hits": forbidden_hits,
        "forbidden_term_count": len(forbidden_hits),
        "bool_checks": bool_checks,
        "residual_checks": residual_checks,
        "gate_results": [asdict(row) for row in gate_rows],
        "source_results": [asdict(row) for row in source_rows],
        "surface": "NSSprint96 Sprint96 KStar collapse constraints fail_closed Clay Navier-Stokes",
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = {"gates": summary["gate_results"], "sources": summary["source_results"]}
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / ROWS_NAME).write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(out_dir / GATE_CSV_NAME, rows["gates"])
    write_csv(out_dir / SOURCE_CSV_NAME, rows["sources"])
    lines = [
        "# NS Sprint 96 K-star Collapse Mechanism Constraints Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Surface: `{summary['surface']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- K-star collapse mechanism closed: `{summary['kstar_collapse_mechanism_closed']}`",
        f"- Required residuals present: `{summary['required_residuals_present_count']}` / `{summary['required_residual_count']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        "",
        "## Required Residuals",
    ]
    lines.extend(f"- {residual}" for residual in summary["required_residuals"])
    lines.extend(["", "## Required Anchors"])
    lines.extend(f"- `{anchor}`" for anchor in summary["required_anchors"])
    (out_dir / REPORT_NAME).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root)
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
