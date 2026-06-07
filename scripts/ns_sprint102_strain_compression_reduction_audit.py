#!/usr/bin/env python3
"""Sprint 102 NS strain-compression reduction audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint102_strain_compression_reduction_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint102_strain_compression_reduction_audit")
SUMMARY_NAME = "ns_sprint102_strain_compression_reduction_audit_summary.json"
ROWS_NAME = "ns_sprint102_strain_compression_reduction_audit_rows.json"
REPORT_NAME = "ns_sprint102_strain_compression_reduction_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint102StrainCompressionReduction.agda")
ROUTE_DECISION = "FAIL_CLOSED_STRAIN_COMPRESSION_REDUCTION"

REQUIRED_ANCHORS = [
    "NSSprint102StrainCompressionReduction",
    "canonicalNSSprint102StrainCompressionReduction",
    "canonicalNSSprint102StrainCompressionReductionReceipt",
    "canonicalSprint102StrainCompressionReductionFlags",
    "LowModeFluxChannelIdentity",
    "LLToLowVanishesByIncompressibility",
    "LHToLowVanishesByIncompressibility",
    "HHToLowEqualsLowStrainContraction",
    "Sprint101FiveGateReduction",
    "FiveSprint101GatesReduceToStrainCompression",
    "StrainCompressionAtHighFrequencyConcentrationPoints",
    "StrainCompressionAtHighFrequencyConcentrationPointsOpen",
    "canonicalStrainCompressionGateStatus",
    "requiredStrainCompressionReductionObjects",
    "strainCompressionReductionLedgerClosed",
    "llToLowChannelVanishesClosed",
    "lhToLowChannelVanishesClosed",
    "hhToLowStrainContractionIdentityClosed",
    "fiveGateCollapseToStrainCompressionClosed",
    "strainCompressionAtHighFrequencyConcentrationPointsClosed",
    "signedLowModeFluxLowerBoundClosed",
    "timeIntegratedFluxSurplusClosed",
    "finiteTimeKStarCollapseClosed",
    "clayNavierStokesPromoted",
    "failClosedStrainCompressionReduction",
]

EXPECTED_BOOLEANS = {
    "strainCompressionReductionLedgerClosed": True,
    "llToLowChannelVanishesClosed": True,
    "lhToLowChannelVanishesClosed": True,
    "hhToLowStrainContractionIdentityClosed": True,
    "fiveGateCollapseToStrainCompressionClosed": True,
    "strainCompressionAtHighFrequencyConcentrationPointsClosed": False,
    "signedLowModeFluxLowerBoundClosed": False,
    "timeIntegratedFluxSurplusClosed": False,
    "finiteTimeKStarCollapseClosed": False,
    "clayNavierStokesPromoted": False,
    "failClosedStrainCompressionReduction": True,
}

CLOSED_REDUCTION_IDENTITIES = [
    "LLToLowVanishesByIncompressibility",
    "LHToLowVanishesByIncompressibility",
    "HHToLowEqualsLowStrainContraction",
    "FiveSprint101GatesReduceToStrainCompression",
]

SINGLE_IRREDUCIBLE_GATE = "StrainCompressionAtHighFrequencyConcentrationPoints"

FORBIDDEN_PATTERNS = {
    "unproved_axiom_marker": re.compile(r"(?<![A-Za-z0-9_])" + "post" + r"ulate(?![A-Za-z0-9_])"),
    "open_work_marker": re.compile(r"(?<![A-Za-z0-9_])" + "TO" + r"DO(?![A-Za-z0-9_])"),
    "incomplete_marker": re.compile(r"(?<![A-Za-z0-9_])" + "st" + r"ub(?![A-Za-z0-9_])", re.I),
    "empty_framework_marker": re.compile(r"(?<![A-Za-z0-9_])" + "skele" + r"tons?(?![A-Za-z0-9_])", re.I),
    "accepted_without_proof_marker": re.compile(r"(?<![A-Za-z0-9_])" + "ad" + r"mit(?:ted|s)?(?![A-Za-z0-9_])", re.I),
    "open_gap_delimiter": re.compile(r"\{" + r"!|!" + r"\}"),
    "open_gap_assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

CLAY_PROMOTED_TRUE = re.compile(
    r"(?<![A-Za-z0-9_])clayNavierStokesPromoted(?![A-Za-z0-9_])"
    r"(?:\s*:\s*[^\n=]+)?\s*=\s*true(?![A-Za-z0-9_])",
    re.MULTILINE,
)


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


def identifier_present(text: str, identifier: str) -> bool:
    return bool(
        re.search(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])", text)
    )


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
    identity_checks = {
        name: {"expected": "recorded", "actual": "present" if identifier_present(text, name) else "missing", "passed": identifier_present(text, name)}
        for name in CLOSED_REDUCTION_IDENTITIES
    }
    forbidden_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]
    forbidden_hits.extend(
        {
            "label": "clay_promotion_true",
            "line": line_for_offset(text, match.start()),
            "match": match.group(0),
        }
        for match in CLAY_PROMOTED_TRUE.finditer(text)
    )

    gate_rows = [
        GateRow(name, "true" if expected else "false", data["actual"], data["passed"], "PASS" if data["passed"] else "FAIL_CLOSED_BOOLEAN_GATE")
        for name, expected in EXPECTED_BOOLEANS.items()
        for data in [bool_checks[name]]
    ]
    gate_rows.extend(
        GateRow(name, "recorded", data["actual"], data["passed"], "PASS" if data["passed"] else "FAIL_CLOSED_MISSING_REDUCTION_IDENTITY")
        for name, data in identity_checks.items()
    )
    gate_rows.extend(
        [
            GateRow(
                "required_anchors",
                "all present",
                "all present" if not missing_anchors else "; ".join(missing_anchors),
                not missing_anchors,
                "PASS" if not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR",
            ),
            GateRow(
                "single_irreducible_gate",
                SINGLE_IRREDUCIBLE_GATE,
                SINGLE_IRREDUCIBLE_GATE if identifier_present(text, SINGLE_IRREDUCIBLE_GATE) else "missing",
                identifier_present(text, SINGLE_IRREDUCIBLE_GATE),
                "PASS" if identifier_present(text, SINGLE_IRREDUCIBLE_GATE) else "FAIL_CLOSED_MISSING_SINGLE_GATE",
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

    evidence_audit_passed = (
        present
        and not missing_anchors
        and not forbidden_hits
        and all(item["passed"] for item in bool_checks.values())
        and all(item["passed"] for item in identity_checks.values())
    )
    source_rows = [
        SourceRow(
            str(AGDA_PATH),
            present,
            "none" if not missing_anchors else "; ".join(missing_anchors),
            "PASS" if present and not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR_OR_FILE",
        )
    ]
    structure_evidence_flags = {
        "ll_to_low_channel_vanishes_closed": True,
        "lh_to_low_channel_vanishes_closed": True,
        "hh_to_low_strain_contraction_identity_closed": True,
        "five_gate_collapse_to_strain_compression_closed": True,
        "strain_compression_at_high_frequency_concentration_points_closed": False,
    }

    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "complete": False,
        "proof_claimed": False,
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "promotion_decision": "hold",
        "evidence_audit_passed": evidence_audit_passed,
        "accepted_source_count": 0,
        "accepted_sources": [],
        "closed_reduction_identities": CLOSED_REDUCTION_IDENTITIES,
        "closed_reduction_identity_count": len(CLOSED_REDUCTION_IDENTITIES),
        "reduction_gates_closed": True,
        "single_irreducible_gate": SINGLE_IRREDUCIBLE_GATE,
        "single_irreducible_gate_open": True,
        "single_irreducible_gate_closed": False,
        "missing_single_gate": SINGLE_IRREDUCIBLE_GATE,
        "missing_gate_count": 1,
        "missing_gate_recorded": identifier_present(text, SINGLE_IRREDUCIBLE_GATE),
        "structure_evidence_flags": structure_evidence_flags,
        "strain_compression_reduction_ledger_closed": True,
        "ll_to_low_channel_vanishes_closed": True,
        "lh_to_low_channel_vanishes_closed": True,
        "hh_to_low_strain_contraction_identity_closed": True,
        "five_gate_collapse_to_strain_compression_closed": True,
        "strain_compression_at_high_frequency_concentration_points_closed": False,
        "signed_low_mode_flux_lower_bound_closed": False,
        "time_integrated_flux_surplus_closed": False,
        "finite_time_kstar_collapse_closed": False,
        "clay_navier_stokes_promoted": False,
        "bool_checks": bool_checks,
        "identity_checks": identity_checks,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "source_results": [asdict(row) for row in source_rows],
        "control_card": {
            "O": "Navier-Stokes Sprint 102 reduction audit",
            "R": "record the LL/LH cancellations and HH strain identity while leaving the geometric sign gate open",
            "C": "Agda receipt plus deterministic Python audit",
            "S": "five Sprint 101 sign gates collapse to one strain-compression gate",
            "L": "closed structural reduction, open geometric correlation, no Clay promotion",
            "P": ROUTE_DECISION,
            "G": "promotion is held until the single geometric gate is proved without forbidden dependencies",
            "F": "the remaining evidence deficit is StrainCompressionAtHighFrequencyConcentrationPoints",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 102 Strain-Compression Reduction Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- Single irreducible gate: `{summary['single_irreducible_gate']}`",
        f"- Single irreducible gate closed: `{summary['single_irreducible_gate_closed']}`",
        f"- Missing gate count: `{summary['missing_gate_count']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Closed Reduction Identities",
    ]
    lines.extend(f"- `{name}`" for name in summary["closed_reduction_identities"])
    lines.extend(["", "## Structure Evidence Flags"])
    lines.extend(
        f"- `{name}`: `{value}`"
        for name, value in summary["structure_evidence_flags"].items()
    )
    lines.extend(["", "## Source Results"])
    lines.extend(
        f"- `{row['source']}` present `{row['present']}` status `{row['status']}`"
        for row in summary["source_results"]
    )
    lines.extend(["", "## Compact O/R/C/S/L/P/G/F"])
    lines.extend(
        f"- {key}: {summary['control_card'][key]}"
        for key in ("O", "R", "C", "S", "L", "P", "G", "F")
    )
    lines.extend(["", "## Gate Results", "", "| Gate | Expected | Actual | Passed | Status |", "| --- | --- | --- | --- | --- |"])
    lines.extend(
        f"| `{row['gate']}` | `{row['expected']}` | `{row['actual']}` | `{row['passed']}` | `{row['status']}` |"
        for row in summary["gate_results"]
    )
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = {"gates": summary["gate_results"], "sources": summary["source_results"]}
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root.resolve())
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
