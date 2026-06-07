#!/usr/bin/env python3
"""Sprint 101 NS signed low-mode flux lower-bound audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint101_signed_low_mode_flux_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint101_signed_low_mode_flux_audit")
SUMMARY_NAME = "ns_sprint101_signed_low_mode_flux_audit_summary.json"
ROWS_NAME = "ns_sprint101_signed_low_mode_flux_audit_rows.json"
REPORT_NAME = "ns_sprint101_signed_low_mode_flux_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint101SignedLowModeFluxLowerBound.agda")
AGDA_GLOB = "NSSprint101*Signed*Low*Mode*Flux*Lower*Bound*.agda"

ROUTE_DECISION = "FAIL_CLOSED_SIGNED_LOW_MODE_FLUX_LOWER_BOUND"
FINAL_DECISION = ROUTE_DECISION

REQUIRED_ANCHORS = [
    "NSSprint101SignedLowModeFluxLowerBound",
    "canonicalNSSprint101SignedLowModeFluxLowerBound",
    "requiredSignedLowModeFluxLowerBoundObjects",
    "SignedLowModeFluxLowerBound",
    "TriadicSignCoherence",
    "LowModeProjectionSignControl",
    "CancellationDefectBound",
    "PressureTransportSignAccounting",
    "NonCircularFluxSignSource",
    "MissingSignedLowModeFluxLowerBoundObject",
    "failClosedSignedLowModeFluxLowerBound",
    "signedLowModeFluxLowerBoundLedgerClosed",
    "signedLowModeFluxLowerBoundClosed",
    "timeIntegratedFluxSurplusClosed",
    "finiteTimeKStarCollapseClosed",
    "clayNavierStokesPromoted",
]

EXPECTED_BOOLEANS = {
    "signedLowModeFluxLowerBoundLedgerClosed": True,
    "signedLowModeFluxLowerBoundClosed": False,
    "timeIntegratedFluxSurplusClosed": False,
    "finiteTimeKStarCollapseClosed": False,
    "clayNavierStokesPromoted": False,
    "failClosedSignedLowModeFluxLowerBound": True,
}

MISSING_ANALYTIC_OBJECTS = [
    "SignedLowModeFluxLowerBound",
    "TriadicSignCoherence",
    "LowModeProjectionSignControl",
    "CancellationDefectBound",
    "PressureTransportSignAccounting",
    "NonCircularFluxSignSource",
]

ANALYTIC_OBJECT_ALIASES = {
    "SignedLowModeFluxLowerBound": [
        "signed low-mode flux lower bound",
        "signed low mode flux lower bound",
        "signed lower bound",
    ],
    "TriadicSignCoherence": [
        "triadic sign coherence",
        "coherent triadic sign",
        "sign coherence",
    ],
    "LowModeProjectionSignControl": [
        "low-mode projection sign control",
        "low mode projection sign control",
        "projection sign control",
    ],
    "CancellationDefectBound": [
        "cancellation defect bound",
        "bound on cancellation defect",
        "cancellation defect",
    ],
    "PressureTransportSignAccounting": [
        "pressure transport sign accounting",
        "pressure-transport sign accounting",
        "pressure transport accounting",
    ],
    "NonCircularFluxSignSource": [
        "non-circular flux sign source",
        "non circular flux sign source",
        "independent flux sign source",
        "independently of the desired collapse conclusion",
    ],
}

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "TODO": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.I),
    "skeleton": re.compile(r"(?<![A-Za-z0-9_])skeletons?(?![A-Za-z0-9_])", re.I),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admit(?:ted|s)?(?![A-Za-z0-9_])", re.I),
    "holes": re.compile(r"\{!|!\}"),
    "hole_assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

CLAY_PROMOTED_TRUE = re.compile(
    r"(?<![A-Za-z0-9_])"
    r"clayNavierStokesPromoted"
    r"(?![A-Za-z0-9_])"
    r"(?:\s*:\s*[^\n=]+)?\s*=\s*true"
    r"(?![A-Za-z0-9_])",
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


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def identifier_present(text: str, identifier: str) -> bool:
    pattern = re.compile(
        r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])"
    )
    return bool(pattern.search(text))


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


def analytic_object_present(text: str, analytic_object: str) -> bool:
    compact_object = re.sub(r"[^A-Za-z0-9]+", "", analytic_object).lower()
    compact_text = re.sub(r"[^A-Za-z0-9]+", "", text).lower()
    return (
        identifier_present(text, analytic_object)
        or compact_object in compact_text
        or any(alias in text for alias in ANALYTIC_OBJECT_ALIASES[analytic_object])
    )


def resolve_agda_path(repo_root: Path) -> tuple[Path, list[str]]:
    exact_path = repo_root / AGDA_PATH
    if exact_path.exists():
        return AGDA_PATH, []

    closure_dir = repo_root / "DASHI" / "Physics" / "Closure"
    candidates = sorted(path for path in closure_dir.glob(AGDA_GLOB) if path.is_file())
    if len(candidates) == 1:
        return candidates[0].relative_to(repo_root), []
    if len(candidates) > 1:
        return AGDA_PATH, [str(path.relative_to(repo_root)) for path in candidates]
    return AGDA_PATH, []


def audit(repo_root: Path) -> dict[str, Any]:
    agda_path, ambiguous_candidates = resolve_agda_path(repo_root)
    path = repo_root / agda_path
    present = path.exists()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""

    missing_anchors = [
        anchor for anchor in REQUIRED_ANCHORS if not identifier_present(text, anchor)
    ]
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
        for analytic_object in MISSING_ANALYTIC_OBJECTS
    }
    forbidden_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]
    clay_promotion_true_hits = [
        {
            "label": "clay_promotion_true",
            "line": line_for_offset(text, match.start()),
            "match": match.group(0),
        }
        for match in CLAY_PROMOTED_TRUE.finditer(text)
    ]
    all_forbidden_hits = forbidden_hits + clay_promotion_true_hits

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
            analytic_object,
            "recorded",
            data["actual"],
            data["passed"],
            "PASS" if data["passed"] else "FAIL_CLOSED_MISSING_EXACT_ANALYTIC_OBJECT",
        )
        for analytic_object, data in analytic_object_checks.items()
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
                "forbidden_markers",
                "none",
                "none" if not all_forbidden_hits else str(len(all_forbidden_hits)),
                not all_forbidden_hits,
                "PASS" if not all_forbidden_hits else "FAIL_CLOSED_FORBIDDEN_MARKER",
            ),
        ]
    )

    source_status = "PASS" if present and not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR_OR_FILE"
    if ambiguous_candidates:
        source_status = "FAIL_CLOSED_AMBIGUOUS_SOURCE"
    source_rows = [
        SourceRow(
            str(agda_path),
            present,
            "none" if not missing_anchors else "; ".join(missing_anchors),
            source_status,
        )
    ]

    evidence_audit_passed = (
        present
        and not ambiguous_candidates
        and not missing_anchors
        and not all_forbidden_hits
        and all(item["passed"] for item in bool_checks.values())
        and all(item["passed"] for item in analytic_object_checks.values())
    )

    return {
        "contract": CONTRACT,
        "agda_path": str(agda_path),
        "canonical_agda_path": str(AGDA_PATH),
        "ambiguous_source_candidates": ambiguous_candidates,
        "complete": False,
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": FINAL_DECISION,
        "promotion_decision": "hold",
        "evidence_audit_passed": evidence_audit_passed,
        "signedLowModeFluxLowerBoundLedgerClosed": True,
        "signedLowModeFluxLowerBoundClosed": False,
        "timeIntegratedFluxSurplusClosed": False,
        "finiteTimeKStarCollapseClosed": False,
        "clayNavierStokesPromoted": False,
        "failClosedSignedLowModeFluxLowerBound": True,
        "signed_low_mode_flux_lower_bound_closed": False,
        "time_integrated_flux_surplus_closed": False,
        "finite_time_kstar_collapse_closed": False,
        "clay_navier_stokes_promoted": False,
        "accepted_source_count": 0,
        "accepted_sources": [],
        "missing_analytic_objects": MISSING_ANALYTIC_OBJECTS,
        "missing_analytic_object_count": len(MISSING_ANALYTIC_OBJECTS),
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
        "forbidden_markers": list(FORBIDDEN_PATTERNS) + ["clay_promotion_true"],
        "forbidden_hits": all_forbidden_hits,
        "forbidden_marker_count": len(all_forbidden_hits),
        "bool_checks": bool_checks,
        "gate_results": [asdict(row) for row in gate_rows],
        "source_results": [asdict(row) for row in source_rows],
        "surface": "NSSprint101 Sprint101 signed low-mode flux lower bound fail_closed Clay Navier-Stokes",
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 101 Signed Low-Mode Flux Lower-Bound Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Surface: `{summary['surface']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- Signed low-mode flux lower bound closed: `{summary['signed_low_mode_flux_lower_bound_closed']}`",
        f"- Time-integrated flux surplus closed: `{summary['time_integrated_flux_surplus_closed']}`",
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
    lines.extend(["", "## Source Results"])
    lines.extend(
        f"- `{row['source']}` present `{row['present']}` status `{row['status']}`"
        for row in summary["source_results"]
    )
    lines.extend(["", "## Gate Results", "", "| Gate | Expected | Actual | Passed | Status |"])
    lines.append("| --- | --- | --- | --- | --- |")
    lines.extend(
        f"| `{row['gate']}` | `{row['expected']}` | `{row['actual']}` | `{row['passed']}` | `{row['status']}` |"
        for row in summary["gate_results"]
    )
    return "\n".join(lines) + "\n"


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
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root)
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
