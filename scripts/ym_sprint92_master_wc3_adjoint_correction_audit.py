#!/usr/bin/env python3
"""Audit Sprint 92 master-WC3 adjoint-scaling correction."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


RECEIPT_PATH = "DASHI/Physics/Closure/YMSprint92MasterWC3AdjointCorrectionReceipt.agda"

ROUTE_OPEN_FAIL_CLOSED = "YM_SPRINT92_ADJOINT_CORRECTION_NUMERIC_BOUNDARY_OPEN"
ROUTE_RECEIPT_MISSING = "YM_SPRINT92_ADJOINT_CORRECTION_RECEIPT_MISSING"
ROUTE_PROMOTION_VIOLATION = "YM_SPRINT92_ADJOINT_CORRECTION_PROMOTION_VIOLATION"

GATE_FIELDS = [
    "gate_id",
    "gate_name",
    "required_anchor",
    "expected_value",
    "actual_value",
    "status",
    "route_decision",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint92_master_wc3_adjoint_correction"),
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def receipt_text(repo_root: Path) -> str | None:
    path = repo_root / RECEIPT_PATH
    if not path.exists():
        return None
    return path.read_text()


def contains(text: str | None, anchor: str) -> bool:
    return text is not None and anchor in text


def route_decision(text: str | None) -> str:
    if text is None:
        return ROUTE_RECEIPT_MISSING
    if "clayYangMillsPromoted = true" in text:
        return ROUTE_PROMOTION_VIOLATION
    return ROUTE_OPEN_FAIL_CLOSED


def gate_rows(text: str | None, route: str) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "ReceiptSurface",
            "canonicalYMSprint92MasterWC3AdjointCorrectionReceipt",
            True,
            contains(text, "canonicalYMSprint92MasterWC3AdjointCorrectionReceipt"),
            "RECEIPT_EXPECTED",
        ),
        (
            "G2",
            "SU2K9Passes",
            "su2K9IntegerInequalityCheck",
            True,
            contains(text, "su2K9IntegerInequalityCheck = refl"),
            "SU2_K9_PASS_EXPECTED",
        ),
        (
            "G3",
            "SU3K9Fails",
            "su3K9IntegerFailureCheck",
            True,
            contains(text, "su3K9IntegerFailureCheck = refl"),
            "SU3_K9_FAIL_EXPECTED",
        ),
        (
            "G4",
            "SU3K10Fails",
            "su3K10IntegerFailureCheck",
            True,
            contains(text, "su3K10IntegerFailureCheck = refl"),
            "SU3_K10_FAIL_EXPECTED",
        ),
        (
            "G5",
            "SU3K11Passes",
            "su3K11IntegerInequalityCheck",
            True,
            contains(text, "su3K11IntegerInequalityCheck = refl"),
            "SU3_K11_PASS_EXPECTED",
        ),
        (
            "G6",
            "QhpWitnessUnexported",
            "balabanQhpLocalConstantBoundWitnessImpossibleHere",
            True,
            contains(text, "balabanQhpLocalConstantBoundWitnessImpossibleHere ()"),
            "ANALYTIC_WITNESS_OPEN_EXPECTED",
        ),
        (
            "G7",
            "PolymerMassWitnessUnexported",
            "balabanCMP116PolymerMassBoundWitnessImpossibleHere",
            True,
            contains(text, "balabanCMP116PolymerMassBoundWitnessImpossibleHere ()"),
            "ANALYTIC_WITNESS_OPEN_EXPECTED",
        ),
        (
            "G8",
            "WC3StillFalse",
            "wc3UniformClusterSummabilitySU3DerivedInRepo = false",
            True,
            contains(text, "wc3UniformClusterSummabilitySU3DerivedInRepo = false"),
            "WC3_FALSE_EXPECTED",
        ),
        (
            "G9",
            "ClayStillFalse",
            "clayYangMillsPromoted = false",
            True,
            contains(text, "clayYangMillsPromoted = false"),
            "CLAY_FALSE_EXPECTED",
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "required_anchor": required_anchor,
            "expected_value": expected_value,
            "actual_value": actual_value,
            "status": status,
            "route_decision": route,
        }
        for (
            gate_id,
            gate_name,
            required_anchor,
            expected_value,
            actual_value,
            status,
        ) in raw_rows
    ]


def summary_payload(repo_root: Path) -> dict[str, Any]:
    text = receipt_text(repo_root)
    route = route_decision(text)
    rows = gate_rows(text, route)
    all_gates_pass = all(row["expected_value"] == row["actual_value"] for row in rows)
    return {
        "receipt_path": RECEIPT_PATH,
        "route_decision": route,
        "all_gates_pass": all_gates_pass,
        "exp_minus_4_enclosure": {
            "lower": "0.018315638",
            "upper": "0.018315639",
        },
        "cases": {
            "su2_k9": {
                "c_local": "1/(2*512) = 0.0009765625",
                "row_sum": "18*C = 0.017578125",
                "status": "passes",
            },
            "su3_k9": {
                "c_local": "2.25/(2*512) = 0.002197265625",
                "row_sum": "18*C = 0.03955078125",
                "status": "fails",
            },
            "su3_k10": {
                "c_local": "2.25/(2*1024) = 0.0010986328125",
                "row_sum": "18*C = 0.019775390625",
                "status": "fails",
            },
            "su3_k11": {
                "c_local": "2.25/(2*2048) = 0.00054931640625",
                "row_sum": "18*C = 0.0098876953125",
                "status": "passes_arithmetically",
            },
        },
        "remaining_open_lemmas": [
            "BalabanQhpLocalConstantBound",
            "BalabanCMP116PolymerMassBound",
            "AdjointRepresentationSharperBound-or-BlockingDepthK11PhysicalValidation",
            "WeakCouplingWindowSU3",
        ],
        "clay_yang_mills_promoted": False,
        "gates": rows,
    }


def write_outputs(payload: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint92_master_wc3_adjoint_correction_summary.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )
    with (out_dir / "ym_sprint92_master_wc3_adjoint_correction_gate_table.csv").open(
        "w", newline=""
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=GATE_FIELDS)
        writer.writeheader()
        writer.writerows(payload["gates"])


def main() -> int:
    args = parse_args()
    payload = summary_payload(args.repo_root)
    write_outputs(payload, args.out_dir)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["all_gates_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
