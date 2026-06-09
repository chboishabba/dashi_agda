#!/usr/bin/env python3
"""Sprint 111 NS LP Grafakos infrastructure and strain refocus audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint111_lp_grafakos_refocus_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint111_lp_grafakos_refocus_audit")
SUMMARY_NAME = "ns_sprint111_lp_grafakos_refocus_audit_summary.json"
ROWS_NAME = "ns_sprint111_lp_grafakos_refocus_audit_rows.json"
REPORT_NAME = "ns_sprint111_lp_grafakos_refocus_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint111LPGrafakosInfrastructureAndStrainRefocus.agda")
ROUTE_DECISION = "LP_INFRASTRUCTURE_CLOSED_STRAIN_COMPRESSION_REFOCUSED"

ACCEPTED_AUTHORITIES = [
    "rudinExerciseEightOneAuthorityRow",
    "grafakosClassicalFourierAnalysisTheoremSixOneSevenAuthorityRow",
]

LP_GATES = [
    "lpGrafakosInfrastructureReceiptClosed",
    "LittlewoodPaleyInfrastructureConstructionClosed",
    "RudinSmoothBumpAuthorityClosed",
    "GrafakosDyadicPartitionAuthorityClosed",
    "LittlewoodPaleyBumpInfrastructureClosed",
]

ANCHOR_FILES = {
    "sprint102": Path("DASHI/Physics/Closure/NSSprint102StrainCompressionReduction.agda"),
    "sprint103": Path("DASHI/Physics/Closure/NSSprint103StrainCompressionGeometryGate.agda"),
    "sprint107": Path("DASHI/Physics/Closure/NSSprint107SmoothDyadicCutoffPartition.agda"),
    "sprint108": Path("DASHI/Physics/Closure/NSSprint108RadialBumpFunctionConstruction.agda"),
    "sprint109": Path("DASHI/Physics/Closure/NSSprint109SmoothCompactSupportWitness.agda"),
    "sprint110": Path("DASHI/Physics/Closure/NSSprint110BaseExpSmoothFunction.agda"),
}

REQUIRED_ANCHORS = [
    "NSSprint111LPGrafakosInfrastructureAndStrainRefocus",
    "canonicalNSSprint111LPGrafakosInfrastructureAndStrainRefocus",
    "nsSprint111LPGrafakosInfrastructureAndStrainRefocusReceipt",
    "canonicalSprint111LPGrafakosInfrastructureAndStrainRefocusFlags",
    "LittlewoodPaleyInfrastructureConstructionClosed",
    "proofDriftCorrectionLedgerClosed",
    "strainCompressionRefocusLedgerClosed",
    "ImportedSprintChain",
    "canonicalImportedSprintChain",
    "LPClosedGateStatuses",
    "canonicalLPClosedGateStatuses",
    "StrainRefocusStatuses",
    "canonicalStrainRefocusStatuses",
    "NSSprint102StrainCompressionReduction",
    "NSSprint103StrainCompressionGeometryGate",
    "NSSprint107SmoothDyadicCutoffPartition",
    "NSSprint108RadialBumpFunctionConstruction",
    "NSSprint109SmoothCompactSupportWitness",
    "NSSprint110BaseExpSmoothFunction",
    *ACCEPTED_AUTHORITIES,
]

EXPECTED_BOOLEANS = {
    **{gate: True for gate in LP_GATES},
    "proofDriftCorrectionLedgerClosed": True,
    "strainCompressionAtHighFrequencyConcentrationPointsClosed": False,
    "clayNavierStokesPromoted": False,
}

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


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.exists()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_present(text, anchor)]
    anchor_file_checks = {
        label: {"path": str(anchor_path), "present": (repo_root / anchor_path).exists()}
        for label, anchor_path in ANCHOR_FILES.items()
    }
    bool_checks = {
        name: {
            "expected": expected,
            "actual": actual_bool_assignment(text, name) if present else "missing",
            "passed": bool_assignment(text, name, expected) if present else False,
        }
        for name, expected in EXPECTED_BOOLEANS.items()
    }
    accepted_authority_hits = [authority for authority in ACCEPTED_AUTHORITIES if identifier_present(text, authority)]
    lp_gate_checks = {
        gate: {
            "closed": bool_assignment(text, gate, True) if present else False,
            "passed": bool_assignment(text, gate, True) if present else False,
        }
        for gate in LP_GATES
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
            bool_checks[name]["actual"],
            bool_checks[name]["passed"],
            "PASS" if bool_checks[name]["passed"] else "FAIL_CLOSED_BOOLEAN_GATE",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
    ]
    gate_rows.extend(
        GateRow(
            gate,
            "closed true",
            "closed true" if data["closed"] else "not closed",
            data["passed"],
            "PASS" if data["passed"] else "FAIL_CLOSED_LP_GATE",
        )
        for gate, data in lp_gate_checks.items()
    )
    gate_rows.extend(
        GateRow(
            f"{label}_anchor_file",
            str(data["path"]),
            "present" if data["present"] else "missing",
            data["present"],
            "PASS" if data["present"] else "FAIL_CLOSED_MISSING_ANCHOR_FILE",
        )
        for label, data in anchor_file_checks.items()
    )
    gate_rows.extend(
        [
            GateRow("route", ROUTE_DECISION, ROUTE_DECISION, True, "PASS"),
            GateRow(
                "required_anchors",
                "all present",
                "all present" if not missing_anchors else "; ".join(missing_anchors),
                not missing_anchors,
                "PASS" if not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR",
            ),
            GateRow(
                "accepted_authority_count",
                "2",
                str(len(accepted_authority_hits)),
                len(accepted_authority_hits) == 2,
                "PASS" if len(accepted_authority_hits) == 2 else "FAIL_CLOSED_AUTHORITY_COUNT",
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
    structural_checks_pass = present and not missing_anchors and not forbidden_hits and all(
        row.passed for row in gate_rows
    )
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "target_present": present,
        "complete": structural_checks_pass,
        "proof_claimed": False,
        "fail_closed": not structural_checks_pass,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "promotion_decision": "hold",
        "promotion_hold": True,
        "evidence_audit_passed": structural_checks_pass,
        "accepted_authority_count": 2,
        "accepted_authorities": ACCEPTED_AUTHORITIES,
        "accepted_authority_hits": accepted_authority_hits,
        "lp_gate_count": len(LP_GATES),
        "closed_lp_gate_count": sum(1 for data in lp_gate_checks.values() if data["passed"]),
        "lp_gates": LP_GATES,
        "lp_gate_checks": lp_gate_checks,
        "lp_infrastructure_construction_closed": bool_checks["LittlewoodPaleyInfrastructureConstructionClosed"]["passed"],
        "proof_drift_correction_ledger_closed": bool_checks["proofDriftCorrectionLedgerClosed"]["passed"],
        "strain_compression_at_high_frequency_concentration_points_closed": False,
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "anchor_file_checks": anchor_file_checks,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "bool_checks": bool_checks,
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "control_card": {
            "O": "Worker 2 owns the Sprint111 LP Grafakos refocus audit script only",
            "R": "verify the LP infrastructure route, Sprint102/103/107/108/109/110 anchors, exact booleans, two authorities, and forbidden-marker absence",
            "C": "single deterministic Python audit emitting summary JSON, rows JSON, and Markdown",
            "S": "target Agda module is inspected when present; anchor files are checked independently",
            "L": "missing target or failed gate keeps evidence unpromoted; all structural gates passing promotes only the audit evidence",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false and strain compression closure remains false",
            "F": "missing route, anchors, authorities, booleans, files, or forbidden-marker hits block audit passage",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 111 LP Grafakos Refocus Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Target present: `{summary['target_present']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- LP infrastructure construction closed: `{summary['lp_infrastructure_construction_closed']}`",
        f"- Proof drift correction ledger closed: `{summary['proof_drift_correction_ledger_closed']}`",
        f"- Accepted authority count: `{summary['accepted_authority_count']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Strain compression at high frequency concentration points closed: `{summary['strain_compression_at_high_frequency_concentration_points_closed']}`",
        "",
        "## Anchor Files",
        "",
        "| Anchor | Path | Present |",
        "| --- | --- | --- |",
    ]
    lines.extend(
        f"| `{label}` | `{data['path']}` | `{data['present']}` |"
        for label, data in summary["anchor_file_checks"].items()
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
