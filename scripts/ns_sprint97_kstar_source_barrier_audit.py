#!/usr/bin/env python3
"""Sprint 97 NS K-star collapse source barrier audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint97_kstar_source_barrier_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint97_kstar_source_barrier_audit")
SUMMARY_NAME = "ns_sprint97_kstar_source_barrier_audit_summary.json"
ROWS_NAME = "ns_sprint97_kstar_source_barrier_audit_rows.json"
GATE_CSV_NAME = "ns_sprint97_kstar_source_barrier_gate_table.csv"
SOURCE_CSV_NAME = "ns_sprint97_kstar_source_barrier_source_table.csv"
REPORT_NAME = "ns_sprint97_kstar_source_barrier_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint97KStarCollapseSourceBarrier.agda")

REQUIRED_ANCHORS = [
    "NSSprint97KStarCollapseSourceBarrier",
    "canonicalNSSprint97KStarCollapseSourceBarrier",
    "KStarCollapseSourceBarrierResiduals",
    "KStarSourceBarrier",
    "failClosedKStarSourceBarrier",
    "CollapseSourceBarrier",
    "canonicalCollapseSourceBarrier",
    "SameSourceCollapseMechanism",
    "canonicalSameSourceCollapseMechanism",
    "RequiredAnalyticObject",
    "requiredAnalyticObjects",
    "CandidateRejectionLedgerEntry",
    "candidateFamilyRejectionLedger",
    "kStarCollapseSourceBarrierLedgerClosed",
    "sameSourceCollapseMechanismAvailable",
    "finiteTimeKStarCollapseClosed",
    "optionBBlowupConstructionClosed",
    "clayNavierStokesPromoted",
]

EXPECTED_BOOLEANS = {
    "kStarCollapseSourceBarrierLedgerClosed": True,
    "sameSourceCollapseMechanismAvailable": False,
    "finiteTimeKStarCollapseClosed": False,
    "optionBBlowupConstructionClosed": False,
    "clayNavierStokesPromoted": False,
}

EXPECTED_NATURALS: dict[str, int] = {}

REQUIRED_ANALYTIC_OBJECTS = [
    "LowModeEnergyConcentrationDynamics",
    "ViscousDampingDefeatEstimate",
    "LerayCompatibleCollapseTrajectory",
    "SingularityExtractionWithoutBKMOrSerrin",
]

ANALYTIC_OBJECT_ALIASES = {
    "LowModeEnergyConcentrationDynamics": [
        "LerayCompatibleLowModeEnergyConcentration",
        "lowModeEnergyConcentrationMechanism",
        "compatibility with Leray energy",
    ],
    "ViscousDampingDefeatEstimate": [
        "ViscousDampingOvercomeMechanism",
        "viscousDampingOvercomeMechanism",
        "viscous damping",
    ],
    "LerayCompatibleCollapseTrajectory": [
        "ScalingCompatibleSelfSimilarity",
        "scalingCompatibleSelfSimilarity",
        "self-similar collapse",
    ],
    "SingularityExtractionWithoutBKMOrSerrin": [
        "CriterionAvoidingSingularityExtractionBridge",
        "singularityExtractionWithoutCriterionFailure",
        "conditional-criterion boundary",
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


def natural_assignment(text: str, name: str, expected: int) -> bool:
    pattern = re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(name)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + re.escape(str(expected))
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )
    return bool(pattern.search(text))


def actual_natural_assignment(text: str, name: str) -> str:
    pattern = re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(name)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*([0-9]+)(?![A-Za-z0-9_])",
        re.MULTILINE,
    )
    match = pattern.search(text)
    return match.group(1) if match else "missing"


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def analytic_object_present(text: str, analytic_object: str) -> bool:
    compact = re.sub(r"[^A-Za-z0-9]+", "", analytic_object).lower()
    surface = re.sub(r"[^A-Za-z0-9]+", "", text).lower()
    camel = analytic_object.title().replace(" ", "").replace("-", "")
    return (
        analytic_object in text
        or compact in surface
        or camel in text
        or any(alias in text for alias in ANALYTIC_OBJECT_ALIASES[analytic_object])
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
    natural_checks = {
        name: {
            "expected": expected,
            "actual": actual_natural_assignment(text, name),
            "passed": natural_assignment(text, name, expected),
        }
        for name, expected in EXPECTED_NATURALS.items()
    }
    analytic_object_checks = {
        analytic_object: {
            "expected": True,
            "actual": "present" if analytic_object_present(text, analytic_object) else "missing",
            "passed": analytic_object_present(text, analytic_object),
        }
        for analytic_object in REQUIRED_ANALYTIC_OBJECTS
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
            name,
            str(expected),
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL",
        )
        for name, expected in EXPECTED_NATURALS.items()
        for data in [natural_checks[name]]
    )
    gate_rows.extend(
        GateRow(
            analytic_object,
            "present",
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL",
        )
        for analytic_object, data in analytic_object_checks.items()
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
        and all(item["passed"] for item in natural_checks.values())
        and all(item["passed"] for item in analytic_object_checks.values())
    )
    analytic_objects_present = [
        analytic_object
        for analytic_object, data in analytic_object_checks.items()
        if data["passed"]
    ]

    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "complete": False,
        "fail_closed": True,
        "route_decision": "FAIL_CLOSED_KSTAR_SOURCE_BARRIER",
        "final_decision": "FAIL_CLOSED_KSTAR_SOURCE_BARRIER",
        "promotion_decision": "hold",
        "evidence_audit_passed": evidence_audit_passed,
        "same_source_collapse_mechanism_available": False,
        "accepted_source_count": 0,
        "accepted_sources": [],
        "clay_navier_stokes_promoted": False,
        "required_analytic_objects": REQUIRED_ANALYTIC_OBJECTS,
        "required_analytic_objects_present": analytic_objects_present,
        "required_analytic_object_count": len(REQUIRED_ANALYTIC_OBJECTS),
        "required_analytic_objects_present_count": len(analytic_objects_present),
        "missing_required_analytic_objects": [
            analytic_object
            for analytic_object, data in analytic_object_checks.items()
            if not data["passed"]
        ],
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "forbidden_hits": forbidden_hits,
        "forbidden_term_count": len(forbidden_hits),
        "bool_checks": bool_checks,
        "natural_checks": natural_checks,
        "analytic_object_checks": analytic_object_checks,
        "gate_results": [asdict(row) for row in gate_rows],
        "source_results": [asdict(row) for row in source_rows],
        "surface": "NSSprint97 Sprint97 KStar collapse source barrier fail_closed Clay Navier-Stokes",
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
        "# NS Sprint 97 K-star Collapse Source Barrier Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Surface: `{summary['surface']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- Same-source collapse mechanism available: `{summary['same_source_collapse_mechanism_available']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Required analytic objects present: `{summary['required_analytic_objects_present_count']}` / `{summary['required_analytic_object_count']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        "",
        "## Required Analytic Objects",
    ]
    lines.extend(f"- {analytic_object}" for analytic_object in summary["required_analytic_objects"])
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
