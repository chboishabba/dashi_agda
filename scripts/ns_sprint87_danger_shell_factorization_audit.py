#!/usr/bin/env python3
"""Sprint 87 NS danger-shell sup-factorization audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint87_danger_shell_factorization_audit"
ROUTE_OPEN = "NS_SPRINT87_DANGER_SHELL_FACTORIZATION_ABSORPTION_OPEN"
SUMMARY_NAME = "ns_sprint87_danger_shell_factorization_summary.json"
REPORT_NAME = "ns_sprint87_danger_shell_factorization_report.md"
ANCHOR_TABLE = "ns_sprint87_danger_shell_factorization_receipt_anchor_table.csv"
GATE_TABLE = "ns_sprint87_danger_shell_factorization_gate_table.csv"

RECEIPT = Path(
    "DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda"
)

REQUIRED_ANCHORS = [
    "canonicalNSSprint87DangerShellSupFactorizationReceipt",
    "dyadicSupFactorizationClosed",
    "shellSupControlledByH1TailClosed",
    "highHighHminusHalfBoundClosed",
    "dangerShellAbsorptionConditionClosed",
    "clayNavierStokesPromoted",
]

BOOL_ASSIGNMENT = re.compile(
    r"(?m)^\s*([A-Za-z][A-Za-z0-9']*)\s*:\s*Bool\s*\n"
    r"\s*\1\s*=\s*(true|false)\s*$"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def read_receipt(repo_root: Path) -> str:
    return (repo_root / RECEIPT).read_text(encoding="utf-8")


def bools(text: str) -> dict[str, bool]:
    return {name: raw == "true" for name, raw in BOOL_ASSIGNMENT.findall(text)}


def anchor_rows(text: str) -> list[dict[str, Any]]:
    return [
        {
            "surface_name": "NSSprint87DangerShellSupFactorizationReceipt",
            "path": RECEIPT.as_posix(),
            "required_anchor": anchor,
            "present_in_receipt": anchor in text,
        }
        for anchor in REQUIRED_ANCHORS
    ]


def gate_rows(values: dict[str, bool]) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "DyadicSupFactorization",
            "dyadicSupFactorizationClosed",
            True,
            False,
            "dyadic supremum pullout is recorded",
        ),
        (
            "G2",
            "ShellSupControlledByH1TailFactorization",
            "shellSupControlledByH1TailClosed",
            True,
            False,
            "weighted shell supremum is controlled by the H1 tail surface",
        ),
        (
            "G3",
            "HighHighHminusHalfFactorization",
            "highHighHminusHalfBoundClosed",
            True,
            False,
            "Hminus-half high-high bound is reduced to the scalar absorption factor",
        ),
        (
            "G4",
            "DangerShellAbsorptionCondition",
            "dangerShellAbsorptionConditionClosed",
            False,
            False,
            "derive scalar absorption inequality uniformly in the NS route",
        ),
        (
            "G5",
            "ClayNavierStokesPromoted",
            "clayNavierStokesPromoted",
            False,
            False,
            "theta/BKM continuation and Clay promotion remain blocked",
        ),
    ]
    rows: list[dict[str, Any]] = []
    for gate_id, gate_name, field, expected, clay_promotion, next_input in raw_rows:
        actual = values.get(field)
        passed = actual is expected
        if gate_name == "ClayNavierStokesPromoted":
            status = "FALSE_NO_PROMOTION" if passed else "PROMOTION_VIOLATION"
        elif expected:
            status = "CLOSED_RECORDED" if passed else "MISSING_CLOSURE"
        else:
            status = "OPEN_FAIL_CLOSED" if passed else "UNEXPECTED_CLOSURE"
        rows.append(
            {
                "gate_id": gate_id,
                "gate_name": gate_name,
                "status": status,
                "field_name": field,
                "actual_value": actual,
                "expected_value": expected,
                "proved_in_repo": actual is True,
                "clay_promotion": clay_promotion,
                "next_required_input": next_input,
            }
        )
    return rows


def build_summary(repo_root: Path) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    text = read_receipt(repo_root)
    anchors = anchor_rows(text)
    values = bools(text)
    gates = gate_rows(values)
    anchors_ok = all(row["present_in_receipt"] for row in anchors)
    clay_promoted = values.get("clayNavierStokesPromoted", False)
    absorption_closed = values.get("dangerShellAbsorptionConditionClosed", False)
    factorization_closed = all(
        values.get(field, False)
        for field in (
            "dyadicSupFactorizationClosed",
            "shellSupControlledByH1TailClosed",
            "highHighHminusHalfBoundClosed",
        )
    )
    summary = {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": ROUTE_OPEN,
        "receipt_path": RECEIPT.as_posix(),
        "all_required_receipt_anchors_present": anchors_ok,
        "factorization_support_closed": factorization_closed,
        "dyadic_sup_factorization_closed": values.get("dyadicSupFactorizationClosed"),
        "shell_sup_controlled_by_h1_tail_closed": values.get(
            "shellSupControlledByH1TailClosed"
        ),
        "high_high_hminus_half_bound_closed": values.get(
            "highHighHminusHalfBoundClosed"
        ),
        "danger_shell_absorption_closed": absorption_closed,
        "danger_shell_absorption_proved_in_repo": absorption_closed,
        "clay_navier_stokes_promoted": clay_promoted,
        "clay_promotion_recorded_false": clay_promoted is False,
        "next_required_gate": "DangerShellAbsorptionCondition",
        "open_obligations": [
            "prove DangerShellH1TailSmallness from non-circular NS inputs",
            "prove the scalar absorption inequality at K*(t)",
            "close KStar drift containment and theta/BKM continuation after absorption",
        ],
    }
    return summary, anchors, gates


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(summary: dict[str, Any], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 87 Danger-Shell Factorization Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route: `{summary['route_decision']}`",
        f"- Factorization support closed: `{summary['factorization_support_closed']}`",
        f"- Absorption closed: `{summary['danger_shell_absorption_closed']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Gates",
        "",
        "| Gate | Status | Value | Next input |",
        "| --- | --- | --- | --- |",
    ]
    for row in gates:
        lines.append(
            f"| `{row['gate_name']}` | `{row['status']}` | "
            f"`{row['actual_value']}` | {row['next_required_input']} |"
        )
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary, anchors, gates = build_summary(args.repo_root)
    write_csv(args.out_dir / ANCHOR_TABLE, anchors)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(markdown(summary, gates), encoding="utf-8")


if __name__ == "__main__":
    main()
