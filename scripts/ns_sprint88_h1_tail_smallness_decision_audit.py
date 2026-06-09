#!/usr/bin/env python3
"""Sprint 88 NS H1-tail smallness decision audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint88_h1_tail_smallness_decision_audit"
ROUTE_OPEN = "NS_SPRINT88_H1_TAIL_SMALLNESS_DECISION_OPEN"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint88_h1_tail_smallness_decision_audit")
SUMMARY_NAME = "ns_sprint88_h1_tail_smallness_decision_summary.json"
SOURCE_TABLE = "ns_sprint88_h1_tail_smallness_decision_source_table.csv"
GATE_TABLE = "ns_sprint88_h1_tail_smallness_decision_gate_table.csv"
REPORT_NAME = "ns_sprint88_h1_tail_smallness_decision_report.md"

RECEIPT_CANDIDATES = [
    Path("DASHI/Physics/Closure/NSSprint88H1TailSmallnessDecisionReceipt.agda"),
    Path("DASHI/Physics/Closure/NSSprint88H1TailSmallnessDecisionAuditReceipt.agda"),
    Path("DASHI/Physics/Closure/NSSprint88DangerShellH1TailSmallnessDecisionReceipt.agda"),
]

SUPPORT_SURFACES = [
    (
        "Sprint87DangerShellSupFactorization",
        "DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda",
        ["canonicalNSSprint87DangerShellSupFactorizationReceipt"],
    ),
    (
        "Sprint86KStarHHalfTailObstruction",
        "DASHI/Physics/Closure/NSSprint86KStarHHalfTailObstructionReceipt.agda",
        ["canonicalNSSprint86KStarHHalfTailObstructionReceipt"],
    ),
]

RECEIPT_ANCHORS = [
    "canonicalNSSprint88H1TailSmallnessDecisionReceipt",
    "sprint87FactorizationInheritedClosed",
    "kStarAdmissibilityAloneInsufficient",
    "lerayEnergyAloneInsufficient",
    "timeIntegratedDissipationPointwiseInsufficient",
    "nonCircularDangerShellH1TailSmallnessClosed",
    "dangerShellAbsorptionConditionClosed",
    "clayNavierStokesPromoted",
]

GATE_SPECS = [
    (
        "G1",
        "Sprint87FactorizationInheritedClosed",
        "sprint87FactorizationInheritedClosed",
        True,
        "Sprint 87 factorization is inherited as a prerequisite only",
    ),
    (
        "G2",
        "KStarAdmissibilityAloneInsufficient",
        "kStarAdmissibilityAloneInsufficient",
        True,
        "K*(t) admissibility alone does not prove H1-tail smallness",
    ),
    (
        "G3",
        "LerayEnergyAloneInsufficient",
        "lerayEnergyAloneInsufficient",
        True,
        "Leray energy alone is not pointwise H1-tail smallness",
    ),
    (
        "G4",
        "TimeIntegratedDissipationPointwiseInsufficient",
        "timeIntegratedDissipationPointwiseInsufficient",
        True,
        "time-integrated dissipation is not a pointwise danger-shell bound",
    ),
    (
        "G5",
        "NonCircularDangerShellH1TailSmallnessClosed",
        "nonCircularDangerShellH1TailSmallnessClosed",
        False,
        "prove non-circular H1-tail smallness without continuation input",
    ),
    (
        "G6",
        "DangerShellAbsorptionConditionClosed",
        "dangerShellAbsorptionConditionClosed",
        False,
        "derive scalar absorption at the danger shell after tail smallness",
    ),
    (
        "G7",
        "ClayNavierStokesPromoted",
        "clayNavierStokesPromoted",
        False,
        "no Clay Navier-Stokes promotion before all blockers close",
    ),
]

BOOL_DECL = re.compile(
    r"(?m)^\s*([A-Za-z][A-Za-z0-9']*)\s*:\s*Bool\s*\n"
    r"\s*\1\s*=\s*(true|false)\s*$"
)
FIELD_ASSIGN = re.compile(r"(?m)^\s*;\s*([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$")
CLAY_TRUE = re.compile(r"(?m)\bclayNavierStokesPromoted\b\s*(?:=|:=[^\n]*=)\s*true\b")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def bools(text: str) -> dict[str, bool]:
    values = {name: raw == "true" for name, raw in BOOL_DECL.findall(text)}
    values.update({name: raw == "true" for name, raw in FIELD_ASSIGN.findall(text)})
    return values


def receipt_path(repo_root: Path) -> Path:
    for rel in RECEIPT_CANDIDATES:
        if (repo_root / rel).exists():
            return rel
    closure_dir = repo_root / "DASHI/Physics/Closure"
    for path in sorted(closure_dir.glob("NSSprint88*.agda")):
        rel = path.relative_to(repo_root)
        text = read_text(path)
        if any(anchor in text for anchor in RECEIPT_ANCHORS):
            return rel
    return RECEIPT_CANDIDATES[0]


def source_rows(repo_root: Path, receipt_rel: Path, receipt_text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    receipt_exists = (repo_root / receipt_rel).exists()
    missing = [anchor for anchor in RECEIPT_ANCHORS if anchor not in receipt_text]
    rows.append(
        {
            "source_id": "S1",
            "surface_name": "Sprint88H1TailSmallnessDecisionReceipt",
            "path": receipt_rel.as_posix(),
            "present_in_repo": receipt_exists,
            "required_anchors": "; ".join(RECEIPT_ANCHORS),
            "missing_anchors": "; ".join(missing) if missing else "none",
            "status": "PASS" if receipt_exists and not missing else "FAIL",
        }
    )
    for index, (name, rel, anchors) in enumerate(SUPPORT_SURFACES, start=2):
        text = read_text(repo_root / rel)
        missing_support = [anchor for anchor in anchors if anchor not in text]
        rows.append(
            {
                "source_id": f"S{index}",
                "surface_name": name,
                "path": rel,
                "present_in_repo": (repo_root / rel).exists(),
                "required_anchors": "; ".join(anchors),
                "missing_anchors": "; ".join(missing_support) if missing_support else "none",
                "status": "PASS" if (repo_root / rel).exists() and not missing_support else "FAIL",
            }
        )
    return rows


def gate_rows(values: dict[str, bool], anchors_ok: bool, clay_true_detected: bool) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for gate_id, gate_name, field, expected, next_input in GATE_SPECS:
        actual = values.get(field)
        passed = anchors_ok and actual is expected
        if gate_name == "ClayNavierStokesPromoted" and clay_true_detected:
            status = "PROMOTION_VIOLATION_FAIL_CLOSED"
            passed = False
        elif not anchors_ok:
            status = "FAIL_CLOSED_MISSING_ANCHOR"
        elif passed and expected is True:
            status = "CLOSED_RECORDED"
        elif passed and expected is False and gate_name == "ClayNavierStokesPromoted":
            status = "FALSE_NO_PROMOTION"
        elif passed and expected is False:
            status = "OPEN_FAIL_CLOSED"
        else:
            status = "VALUE_MISMATCH_FAIL_CLOSED"
        rows.append(
            {
                "gate_id": gate_id,
                "gate_name": gate_name,
                "field_name": field,
                "actual_value": actual,
                "expected_value": expected,
                "passed": passed,
                "status": status,
                "clay_promotion": gate_name == "ClayNavierStokesPromoted" and actual is True,
                "next_required_input": next_input,
            }
        )
    return rows


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def build(repo_root: Path) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    receipt_rel = receipt_path(repo_root)
    text = read_text(repo_root / receipt_rel)
    values = bools(text)
    sources = source_rows(repo_root, receipt_rel, text)
    anchors_ok = sources[0]["status"] == "PASS"
    clay_true_detected = bool(CLAY_TRUE.search(text)) or values.get("clayNavierStokesPromoted") is True
    gates = gate_rows(values, anchors_ok, clay_true_detected)
    fail_closed = (not anchors_ok) or clay_true_detected or any(not row["passed"] for row in gates)
    summary = {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": "fail_closed" if fail_closed else ROUTE_OPEN,
        "receipt_path": receipt_rel.as_posix(),
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "all_required_receipt_anchors_present": anchors_ok,
        "fail_closed": fail_closed,
        "clay_true_detected": clay_true_detected,
        "sprint87_factorization_inherited_closed": values.get("sprint87FactorizationInheritedClosed"),
        "kstar_admissibility_alone_insufficient": values.get("kStarAdmissibilityAloneInsufficient"),
        "leray_energy_alone_insufficient": values.get("lerayEnergyAloneInsufficient"),
        "time_integrated_dissipation_pointwise_insufficient": values.get(
            "timeIntegratedDissipationPointwiseInsufficient"
        ),
        "non_circular_danger_shell_h1_tail_smallness_closed": values.get(
            "nonCircularDangerShellH1TailSmallnessClosed"
        ),
        "danger_shell_absorption_condition_closed": values.get("dangerShellAbsorptionConditionClosed"),
        "clay_navier_stokes_promoted": values.get("clayNavierStokesPromoted"),
        "expected_gates": {gate_name: expected for _, gate_name, _, expected, _ in GATE_SPECS},
        "gate_results": gates,
        "source_results": sources,
        "open_obligations": [
            "materialize all Sprint 88 receipt anchors if missing",
            "prove non-circular danger-shell H1-tail smallness from admissible inputs",
            "derive the danger-shell absorption condition only after non-circular tail smallness",
            "keep Clay Navier-Stokes promotion false until all analytic blockers close",
        ],
    }
    return summary, sources, gates


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 88 H1-Tail Smallness Decision Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Receipt: `{summary['receipt_path']}`",
        f"- Anchors present: `{summary['all_required_receipt_anchors_present']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        "",
        "## Gates",
        "",
        "| Gate | Expected | Actual | Status |",
        "| --- | --- | --- | --- |",
    ]
    for row in gates:
        lines.append(
            f"| `{row['gate_name']}` | `{row['expected_value']}` | "
            f"`{row['actual_value']}` | `{row['status']}` |"
        )
    lines.extend(["", "## Source Surfaces", ""])
    for row in sources:
        lines.append(
            f"- `{row['source_id']}` `{row['path']}`: `{row['status']}`, "
            f"missing anchors `{row['missing_anchors']}`."
        )
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary, sources, gates = build(args.repo_root)
    write_csv(args.out_dir / SOURCE_TABLE, sources)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(markdown(summary, sources, gates), encoding="utf-8")


if __name__ == "__main__":
    main()
