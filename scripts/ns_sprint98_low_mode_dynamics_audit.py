#!/usr/bin/env python3
"""Sprint 98 NS low-mode energy concentration dynamics audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint98_low_mode_dynamics_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint98_low_mode_dynamics_audit")
SUMMARY_NAME = "ns_sprint98_low_mode_dynamics_audit_summary.json"
ROWS_NAME = "ns_sprint98_low_mode_dynamics_audit_rows.json"
REPORT_NAME = "ns_sprint98_low_mode_dynamics_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint98LowModeEnergyConcentrationDynamics.agda")

ROUTE_DECISION = "FAIL_CLOSED_LOW_MODE_DYNAMICS"
FINAL_DECISION = "FAIL_CLOSED_LOW_MODE_DYNAMICS"

REQUIRED_ANCHORS = [
    "NSSprint98LowModeEnergyConcentrationDynamics",
    "canonicalNSSprint98LowModeEnergyConcentrationDynamics",
    "requiredLowModeDynamicsObjects",
    "LowModeEnergyConcentrationDynamics",
    "InterShellFluxToLowModes",
    "LowModeResidenceTime",
    "InverseCascadeCoherence",
    "LerayEnergyBudgetCompatibility",
    "KStarCollapseForcingInequality",
    "MissingLowModeDynamicsObject",
    "QuantitativeLowModeFluxLowerBound",
    "ResidenceTimeAgainstViscosity",
    "CoherentInverseCascadeMechanism",
    "NonCircularKStarForcing",
    "failClosedLowModeEnergyConcentrationDynamics",
    "lowModeEnergyConcentrationDynamicsLedgerClosed",
    "lowModeEnergyConcentrationDynamicsClosed",
    "finiteTimeKStarCollapseClosed",
    "clayNavierStokesPromoted",
]

EXPECTED_BOOLEANS = {
    "lowModeEnergyConcentrationDynamicsLedgerClosed": True,
    "lowModeEnergyConcentrationDynamicsClosed": False,
    "finiteTimeKStarCollapseClosed": False,
    "clayNavierStokesPromoted": False,
}

EXACT_MISSING_ANALYTIC_OBJECTS = [
    "QuantitativeLowModeFluxLowerBound",
    "ResidenceTimeAgainstViscosity",
    "CoherentInverseCascadeMechanism",
    "NonCircularKStarForcing",
]

ANALYTIC_OBJECT_ALIASES = {
    "QuantitativeLowModeFluxLowerBound": [
        "quantitative low-mode flux lower bound",
        "quantitative low mode flux lower bound",
    ],
    "ResidenceTimeAgainstViscosity": [
        "residence-time estimate",
        "residence time against viscosity",
    ],
    "CoherentInverseCascadeMechanism": [
        "coherent inverse-cascade mechanism",
        "coherent inverse cascade mechanism",
    ],
    "NonCircularKStarForcing": [
        "non-circular forcing inequality",
        "non circular K-star forcing",
    ],
}

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "TODO": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.I),
    "skeleton": re.compile(r"(?<![A-Za-z0-9_])skeleton(?![A-Za-z0-9_])", re.I),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admit(?:ted|s)?(?![A-Za-z0-9_])", re.I),
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


def analytic_object_present(text: str, analytic_object: str) -> bool:
    compact_object = re.sub(r"[^A-Za-z0-9]+", "", analytic_object).lower()
    compact_text = re.sub(r"[^A-Za-z0-9]+", "", text).lower()
    return (
        analytic_object in text
        or compact_object in compact_text
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
    analytic_object_checks = {
        analytic_object: {
            "expected": "recorded",
            "actual": "present" if analytic_object_present(text, analytic_object) else "missing",
            "passed": analytic_object_present(text, analytic_object),
        }
        for analytic_object in EXACT_MISSING_ANALYTIC_OBJECTS
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
            "PASS" if data["passed"] else "FAIL_CLOSED",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
        for data in [bool_checks[name]]
    ]
    gate_rows.extend(
        GateRow(
            analytic_object,
            "recorded",
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL_CLOSED_MISSING_EXACT_ANALYTIC_OBJECT",
        )
        for analytic_object, data in analytic_object_checks.items()
    )
    source_rows = [
        SourceRow(
            str(AGDA_PATH),
            present,
            "none" if not missing_anchors else "; ".join(missing_anchors),
            "PASS" if present and not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR_OR_FILE",
        )
    ]

    evidence_audit_passed = (
        present
        and not missing_anchors
        and not forbidden_hits
        and all(item["passed"] for item in bool_checks.values())
        and all(item["passed"] for item in analytic_object_checks.values())
    )

    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "complete": False,
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": FINAL_DECISION,
        "promotion_decision": "hold",
        "evidence_audit_passed": evidence_audit_passed,
        "low_mode_energy_concentration_dynamics_closed": False,
        "finite_time_kstar_collapse_closed": False,
        "clay_navier_stokes_promoted": False,
        "accepted_source_count": 0,
        "accepted_sources": [],
        "missing_analytic_objects": EXACT_MISSING_ANALYTIC_OBJECTS,
        "missing_analytic_object_count": len(EXACT_MISSING_ANALYTIC_OBJECTS),
        "missing_analytic_objects_recorded": [
            analytic_object
            for analytic_object, data in analytic_object_checks.items()
            if data["passed"]
        ],
        "unrecorded_missing_analytic_objects": [
            analytic_object
            for analytic_object, data in analytic_object_checks.items()
            if not data["passed"]
        ],
        "missing_analytic_object_checks": analytic_object_checks,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "forbidden_markers": list(FORBIDDEN_PATTERNS),
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "bool_checks": bool_checks,
        "gate_results": [asdict(row) for row in gate_rows],
        "source_results": [asdict(row) for row in source_rows],
        "surface": "NSSprint98 Sprint98 low-mode energy concentration dynamics fail_closed Clay Navier-Stokes",
    }


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

    lines = [
        "# NS Sprint 98 Low-Mode Energy Concentration Dynamics Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Surface: `{summary['surface']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- Low-mode energy concentration dynamics closed: `{summary['low_mode_energy_concentration_dynamics_closed']}`",
        f"- Finite-time K-star collapse closed: `{summary['finite_time_kstar_collapse_closed']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- Forbidden marker count: `{summary['forbidden_marker_count']}`",
        "",
        "## Missing Analytic Objects",
    ]
    lines.extend(f"- `{analytic_object}`" for analytic_object in summary["missing_analytic_objects"])
    lines.extend(["", "## Required Anchors"])
    lines.extend(f"- `{anchor}`" for anchor in summary["required_anchors"])
    lines.extend(["", "## Boolean Gates"])
    lines.extend(
        f"- `{name}` expected `{data['expected']}` actual `{data['actual']}` passed `{data['passed']}`"
        for name, data in summary["bool_checks"].items()
    )
    (out_dir / REPORT_NAME).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root)
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
