#!/usr/bin/env python3
"""Sprint 87 NS danger-shell absorption scaling audit."""

from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint87_absorption_scaling_audit"
ROUTE_OPEN = "NS_SPRINT87_ABSORPTION_SCALING_OPEN"
SUMMARY_NAME = "ns_sprint87_absorption_scaling_summary.json"
SOURCE_TABLE = "ns_sprint87_absorption_scaling_source_surface_table.csv"
GATE_TABLE = "ns_sprint87_absorption_scaling_gate_table.csv"
REPORT_NAME = "ns_sprint87_absorption_scaling_report.md"

SCALAR_CONDITION = "(K*)^-1/2 * H1Tail <= epsilon * nu"

LAWS = [
    ("NuInverseAbsorptionLaw", "nu^-1", Fraction(1, 1)),
    ("NuFourThirdsInverseAbsorptionLaw", "nu^-4/3", Fraction(4, 3)),
    ("NuSquaredInverseAbsorptionLaw", "nu^-2", Fraction(2, 1)),
]

SOURCE_SURFACES = [
    (
        "Sprint87AbsorptionScalingAudit",
        "scripts/ns_sprint87_absorption_scaling_audit.py",
        "SCALAR_CONDITION",
        True,
    ),
    (
        "Sprint86KStarHHalfTailObstruction",
        "DASHI/Physics/Closure/NSSprint86KStarHHalfTailObstructionReceipt.agda",
        "canonicalNSSprint86KStarHHalfTailObstructionReceipt",
        True,
    ),
    (
        "Sprint84OneSobolevGapTarget",
        "DASHI/Physics/Closure/NSSprint84HminusHalfOneSobolevGapTargetReceipt.agda",
        "canonicalNSSprint84HminusHalfOneSobolevGapTargetReceipt",
        True,
    ),
    (
        "Sprint87DangerShellSupFactorization",
        "DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda",
        "dangerShellAbsorptionConditionClosed",
        True,
    ),
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def frac(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def source_rows(repo_root: Path) -> list[dict[str, Any]]:
    rows = []
    for name, rel, anchor, expected in SOURCE_SURFACES:
        path = repo_root / rel
        text = path.read_text(encoding="utf-8") if path.exists() else ""
        rows.append(
            {
                "surface_name": name,
                "path": rel,
                "required_anchor": anchor,
                "present_in_repo": path.exists() and anchor in text,
                "expected_present": expected,
                "route_decision": ROUTE_OPEN,
            }
        )
    return rows


def scaling_gate_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for gate_name, law, a in LAWS:
        no_tail_gain_exponent = a / 2
        rows.append(
            {
                "gate_name": gate_name,
                "scaling_law": law,
                "kstar_exponent_a": frac(a),
                "no_tail_gain_left_exponent": frac(no_tail_gain_exponent),
                "required_tail_exponent_b_strict": f"> {frac(1 - a / 2)}",
                "status": "RECORDED_CONDITIONAL",
                "proved_in_repo": False,
                "clay_promotion": False,
                "next_required_input": (
                    "prove non-circular H1 tail smallness with enough nu gain"
                ),
            }
        )
    rows.extend(
        [
            {
                "gate_name": "RequiredScalarAbsorptionCondition",
                "scaling_law": SCALAR_CONDITION,
                "kstar_exponent_a": "",
                "no_tail_gain_left_exponent": "",
                "required_tail_exponent_b_strict": "",
                "status": "NAMED_OPEN",
                "proved_in_repo": False,
                "clay_promotion": False,
                "next_required_input": (
                    "derive scalar absorption inequality uniformly in the NS route"
                ),
            },
            {
                "gate_name": "UnconditionalAbsorptionClosed",
                "scaling_law": "all recorded laws",
                "kstar_exponent_a": "",
                "no_tail_gain_left_exponent": "",
                "required_tail_exponent_b_strict": "",
                "status": "FALSE_FAIL_CLOSED",
                "proved_in_repo": False,
                "clay_promotion": False,
                "next_required_input": "DangerShellH1TailSmallness",
            },
            {
                "gate_name": "ClayNavierStokesPromoted",
                "scaling_law": "not promoted",
                "kstar_exponent_a": "",
                "no_tail_gain_left_exponent": "",
                "required_tail_exponent_b_strict": "",
                "status": "FALSE_NO_PROMOTION",
                "proved_in_repo": False,
                "clay_promotion": False,
                "next_required_input": (
                    "absorption, drift containment, theta/BKM continuation, and review"
                ),
            },
        ]
    )
    return rows


def summary(repo_root: Path) -> dict[str, Any]:
    sources = source_rows(repo_root)
    return {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": ROUTE_OPEN,
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "absorption_scaling_laws_recorded": ["nu^-1", "nu^-4/3", "nu^-2"],
        "nu_inverse_absorption_law_recorded": True,
        "nu_four_thirds_inverse_absorption_law_recorded": True,
        "nu_squared_inverse_absorption_law_recorded": True,
        "required_scalar_condition_name": "RequiredScalarAbsorptionCondition",
        "required_scalar_condition_named": True,
        "required_scalar_condition": SCALAR_CONDITION,
        "unconditional_absorption_closed": False,
        "clay_navier_stokes_promoted": False,
        "clay_promotion_recorded_false": True,
        "all_required_source_surfaces_present": all(
            row["present_in_repo"] for row in sources
        ),
        "scaling_rule": (
            "For K*(nu)=nu^-a and H1Tail<=C*nu^b, absorption requires "
            "b+a/2>1, or b+a/2=1 with an independent C<=epsilon coefficient."
        ),
        "open_obligations": [
            "prove DangerShellH1TailSmallness without using H1/Serrin/BKM continuation",
            "check coefficient smallness at the critical exponent",
            "exclude deriving the H1 tail law from the same absorption inequality",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(payload: dict[str, Any], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 87 Absorption Scaling Audit",
        "",
        f"- Contract: `{payload['contract']}`",
        f"- Route: `{payload['route_decision']}`",
        f"- Scalar condition: `{payload['required_scalar_condition']}`",
        f"- Unconditional absorption closed: `{payload['unconditional_absorption_closed']}`",
        f"- Clay Navier-Stokes promoted: `{payload['clay_navier_stokes_promoted']}`",
        "",
        "## Scaling Laws",
        "",
        "| Gate | Law | Required tail exponent | Status |",
        "| --- | --- | --- | --- |",
    ]
    for row in gates:
        lines.append(
            f"| `{row['gate_name']}` | `{row['scaling_law']}` | "
            f"`{row['required_tail_exponent_b_strict']}` | `{row['status']}` |"
        )
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in payload["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    sources = source_rows(args.repo_root)
    gates = scaling_gate_rows()
    payload = summary(args.repo_root)
    write_csv(args.out_dir / SOURCE_TABLE, sources)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(markdown(payload, gates), encoding="utf-8")


if __name__ == "__main__":
    main()
