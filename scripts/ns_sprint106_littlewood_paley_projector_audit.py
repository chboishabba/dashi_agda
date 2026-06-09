#!/usr/bin/env python3
"""Sprint 106 NS Littlewood-Paley shell projector audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint106_littlewood_paley_projector_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint106_littlewood_paley_projector_audit")
SUMMARY_NAME = "ns_sprint106_littlewood_paley_projector_audit_summary.json"
ROWS_NAME = "ns_sprint106_littlewood_paley_projector_audit_rows.json"
REPORT_NAME = "ns_sprint106_littlewood_paley_projector_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint106LittlewoodPaleyShellProjector.agda")
ROUTE_DECISION = "FAIL_CLOSED_LITTLEWOOD_PALEY_SHELL_PROJECTOR"

SUBGATES = [
    "SmoothDyadicCutoffPartition",
    "FourierMultiplierBoundedness",
    "LerayCompatibleProjection",
    "DivergenceFreeProjectionCommutation",
    "NonCircularProjectorConstruction",
]

EXPECTED_BOOLEANS = {
    "littlewoodPaleyShellProjectorDecompositionLedgerClosed": True,
    "smoothDyadicCutoffPartitionClosed": False,
    "fourierMultiplierBoundednessClosed": False,
    "lerayCompatibleProjectionClosed": False,
    "divergenceFreeProjectionCommutationClosed": False,
    "nonCircularProjectorConstructionClosed": False,
    "littlewoodPaleyShellProjectorClosed": False,
    "dyadicShellEnergyDensityClosed": False,
    "highFrequencyConcentrationMeasureClosed": False,
    "strainCompressionAtHighFrequencyConcentrationPointsClosed": False,
    "signedLowModeFluxLowerBoundClosed": False,
    "timeIntegratedFluxSurplusClosed": False,
    "finiteKStarCollapseClosed": False,
    "clayNavierStokesPromoted": False,
    "failClosedLittlewoodPaleyShellProjectorDecomposition": True,
}

REQUIRED_ANCHORS = [
    "NSSprint106LittlewoodPaleyShellProjector",
    "canonicalNSSprint106LittlewoodPaleyShellProjector",
    "canonicalNSSprint106LittlewoodPaleyShellProjectorReceipt",
    "canonicalSprint106LittlewoodPaleyShellProjectorFlags",
    "LittlewoodPaleyShellProjectorDecomposition",
    "LittlewoodPaleyShellProjectorSplitsIntoFiveSubgates",
    "Sprint105LittlewoodPaleyShellProjectorAnchor",
    "canonicalSprint105LittlewoodPaleyShellProjectorAnchor",
    "LittlewoodPaleyProjectorSubgateStatus",
    "canonicalLittlewoodPaleyShellProjectorDecompositionStatus",
    "requiredLittlewoodPaleyShellProjectorSubgates",
    *SUBGATES,
    *(name + "Open" for name in SUBGATES),
    *EXPECTED_BOOLEANS,
]

TOKEN_UNPROVED = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_EMPTY_FRAME = "skele" + "ton"
TOKEN_ACCEPT_WITHOUT_PROOF = "ad" + "mit"
FORBIDDEN_PATTERNS = {
    "unproved_axiom_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_UNPROVED + r"(?![A-Za-z0-9_])"),
    "open_work_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_OPEN_WORK + r"(?![A-Za-z0-9_])"),
    "incomplete_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])", re.I),
    "empty_framework_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_EMPTY_FRAME + r"s?(?![A-Za-z0-9_])", re.I),
    "accepted_without_proof_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_ACCEPT_WITHOUT_PROOF + r"(?:ted|s)?(?![A-Za-z0-9_])", re.I),
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


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def subgate_bool_name(name: str) -> str:
    return name[0].lower() + name[1:] + "Closed"


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.exists()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_present(text, anchor)]
    bool_checks = {
        name: {
            "expected": expected,
            "actual": actual_bool_assignment(text, name),
            "passed": bool_assignment(text, name, expected),
        }
        for name, expected in EXPECTED_BOOLEANS.items()
    }
    subgate_checks = {
        name: {
            "recorded": identifier_present(text, name),
            "closed_true": bool_assignment(text, subgate_bool_name(name), True),
            "closed_false": bool_assignment(text, subgate_bool_name(name), False),
        }
        for name in SUBGATES
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
            "PASS" if data["passed"] else "FAIL_CLOSED_BOOLEAN_GATE",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
        for data in [bool_checks[name]]
    ]
    gate_rows.extend(
        GateRow(
            name,
            "recorded and false",
            "recorded and false" if data["recorded"] and data["closed_false"] else "missing or not false",
            data["recorded"] and data["closed_false"],
            "PASS" if data["recorded"] and data["closed_false"] else "FAIL_CLOSED_SUBGATE",
        )
        for name, data in subgate_checks.items()
    )
    gate_rows.append(
        GateRow(
            "required_anchors",
            "all present",
            "all present" if not missing_anchors else "; ".join(missing_anchors),
            not missing_anchors,
            "PASS" if not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR",
        )
    )
    gate_rows.append(
        GateRow(
            "forbidden_markers",
            "none",
            "none" if not forbidden_hits else str(len(forbidden_hits)),
            not forbidden_hits,
            "PASS" if not forbidden_hits else "FAIL_CLOSED_FORBIDDEN_MARKER",
        )
    )
    ledger_true = bool_checks["littlewoodPaleyShellProjectorDecompositionLedgerClosed"]["passed"]
    all_subgates_false = all(item["closed_false"] and not item["closed_true"] for item in subgate_checks.values())
    evidence_audit_passed = (
        present
        and not missing_anchors
        and not forbidden_hits
        and all(item["passed"] for item in bool_checks.values())
        and all(item["recorded"] and item["closed_false"] for item in subgate_checks.values())
    )
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "target_present": present,
        "complete": False,
        "proof_claimed": False,
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "promotion_decision": "hold",
        "promotion_hold": True,
        "evidence_audit_passed": evidence_audit_passed,
        "accepted_source_count": 0,
        "accepted_sources": [],
        "littlewood_paley_shell_projector_decomposition_ledger_closed": ledger_true,
        "decomposition_ledger_closed": ledger_true,
        "projector_ledger_closed": ledger_true,
        "littlewood_paley_shell_projector_closed": False,
        "dyadic_shell_energy_density_closed": False,
        "high_frequency_concentration_measure_closed": False,
        "subgates": SUBGATES,
        "open_subgate_count": len(SUBGATES),
        "closed_subgate_count": 0,
        "subgate_smooth_dyadic_cutoff_partition_open": True,
        "subgate_fourier_multiplier_boundedness_open": True,
        "subgate_leray_compatible_projection_open": True,
        "subgate_divergence_free_projection_commutation_open": True,
        "subgate_non_circular_projector_construction_open": True,
        "all_subgates_false": all_subgates_false,
        "all_subgates_closed": False,
        "strain_compression_at_high_frequency_concentration_points_closed": False,
        "signed_low_mode_flux_lower_bound_closed": False,
        "time_integrated_flux_surplus_closed": False,
        "finite_kstar_collapse_closed": False,
        "clay_navier_stokes_promoted": False,
        "bool_checks": bool_checks,
        "subgate_checks": subgate_checks,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 106 Littlewood-Paley Shell Projector Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Target present: `{summary['target_present']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Promotion decision: `{summary['promotion_decision']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Littlewood-Paley shell projector decomposition ledger closed: `{summary['littlewood_paley_shell_projector_decomposition_ledger_closed']}`",
        f"- All subgates false: `{summary['all_subgates_false']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Open Littlewood-Paley Shell Projector Subgates",
    ]
    lines.extend(f"- `{name}`" for name in summary["subgates"])
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
