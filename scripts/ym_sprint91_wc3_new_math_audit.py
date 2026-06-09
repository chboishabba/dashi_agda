#!/usr/bin/env python3
"""Sprint 91 YM WC3 new-math receipt audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


RECEIPT_PATH = (
    "DASHI/Physics/Closure/YMSprint91WC3NewMathReceipt.agda"
)

ROUTE_OPEN_FAIL_CLOSED = "YM_SPRINT91_WC3_NEW_MATH_OPEN_FAIL_CLOSED"
ROUTE_RECEIPT_MISSING = "YM_SPRINT91_WC3_NEW_MATH_RECEIPT_MISSING"
ROUTE_PROMOTION_VIOLATION = "YM_SPRINT91_WC3_NEW_MATH_PROMOTION_VIOLATION"

THEOREM_FIELDS = [
    "theorem_id",
    "theorem_name",
    "required_anchor",
    "expected_status",
    "present_in_receipt",
    "closed_conditionally",
    "proved_in_repo",
    "route_decision",
]

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
        default=Path("outputs/ym_sprint91_wc3_new_math"),
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def theorem_specs() -> list[dict[str, Any]]:
    return [
        {
            "theorem_id": "T1",
            "theorem_name": "CauchySchwarzContraction",
            "required_anchor": "t1CauchySchwarzContractionClosedConditionally",
            "expected_status": "CLOSED_CONDITIONALLY",
            "closed_conditionally": True,
            "proved_in_repo": False,
        },
        {
            "theorem_id": "T2",
            "theorem_name": "MasterCondition",
            "required_anchor": "t2MasterConditionOpen",
            "expected_status": "OPEN",
            "closed_conditionally": False,
            "proved_in_repo": False,
        },
        {
            "theorem_id": "T3",
            "theorem_name": "WC3Derived",
            "required_anchor": "t3WC3DerivedFalse",
            "expected_status": "FALSE_NOT_DERIVED",
            "closed_conditionally": False,
            "proved_in_repo": False,
        },
        {
            "theorem_id": "T4",
            "theorem_name": "ClayPromoted",
            "required_anchor": "t4ClayPromotedFalse",
            "expected_status": "FALSE_NO_PROMOTION",
            "closed_conditionally": False,
            "proved_in_repo": False,
        },
        {
            "theorem_id": "T5",
            "theorem_name": "TheoremListComplete",
            "required_anchor": "t5TheoremListT1ToT5Present",
            "expected_status": "THEOREM_LIST_PRESENT",
            "closed_conditionally": False,
            "proved_in_repo": False,
        },
    ]


def receipt_text(repo_root: Path) -> str | None:
    path = repo_root / RECEIPT_PATH
    if not path.exists():
        return None
    return path.read_text()


def contains_anchor(text: str | None, anchor: str) -> bool:
    return text is not None and anchor in text


def has_all_theorem_ids(text: str | None) -> bool:
    return text is not None and all(theorem_id in text for theorem_id in ["T1", "T2", "T3", "T4", "T5"])


def choose_route(*, receipt_present: bool, clay_promoted: bool) -> str:
    if clay_promoted:
        return ROUTE_PROMOTION_VIOLATION
    if not receipt_present:
        return ROUTE_RECEIPT_MISSING
    return ROUTE_OPEN_FAIL_CLOSED


def theorem_rows(text: str | None, route_decision: str) -> list[dict[str, Any]]:
    return [
        {
            **row,
            "present_in_receipt": contains_anchor(text, row["required_anchor"]),
            "route_decision": route_decision,
        }
        for row in theorem_specs()
    ]


def gate_rows(
    *,
    text: str | None,
    route_decision: str,
    t1_closed_conditionally: bool,
    master_condition_open: bool,
    wc3_derived_false: bool,
    clay_promoted_false: bool,
    theorem_list_present: bool,
) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "ReceiptSurface",
            "canonicalYMSprint91WC3NewMathReceipt",
            True,
            contains_anchor(text, "canonicalYMSprint91WC3NewMathReceipt"),
            "FUTURE_RECEIPT_EXPECTED",
        ),
        (
            "G2",
            "T1CauchySchwarzContractionClosedConditionally",
            "t1CauchySchwarzContractionClosedConditionally",
            True,
            t1_closed_conditionally,
            "CLOSED_CONDITIONALLY_EXPECTED",
        ),
        (
            "G3",
            "MasterConditionOpen",
            "masterConditionOpen",
            True,
            master_condition_open,
            "OPEN_EXPECTED",
        ),
        (
            "G4",
            "WC3DerivedFalse",
            "wc3DerivedFalse",
            True,
            wc3_derived_false,
            "FALSE_EXPECTED",
        ),
        (
            "G5",
            "ClayPromotedFalse",
            "clayPromotedFalse",
            True,
            clay_promoted_false,
            "FALSE_EXPECTED",
        ),
        (
            "G6",
            "TheoremListT1ToT5Present",
            "theoremListT1ToT5Present",
            True,
            theorem_list_present,
            "T1_TO_T5_EXPECTED",
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
            "route_decision": route_decision,
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
    receipt_present = text is not None
    t1_closed_conditionally = contains_anchor(
        text, "t1CauchySchwarzContractionClosedConditionally"
    )
    master_condition_open = contains_anchor(text, "masterConditionOpen") or contains_anchor(
        text, "t2MasterConditionOpen"
    )
    wc3_derived = contains_anchor(text, "wc3DerivedTrue")
    wc3_derived_false = contains_anchor(text, "wc3DerivedFalse") or contains_anchor(
        text, "t3WC3DerivedFalse"
    )
    clay_promoted = contains_anchor(text, "clayPromotedTrue")
    clay_promoted_false = contains_anchor(text, "clayPromotedFalse") or contains_anchor(
        text, "t4ClayPromotedFalse"
    )
    theorem_list_present = (
        has_all_theorem_ids(text)
        and contains_anchor(text, "theoremListT1ToT5Present")
    )
    route_decision = choose_route(
        receipt_present=receipt_present,
        clay_promoted=clay_promoted,
    )
    expected_theorem_anchors = [
        row["required_anchor"] for row in theorem_specs()
    ]
    present_theorem_anchors = [
        anchor for anchor in expected_theorem_anchors if contains_anchor(text, anchor)
    ]

    return {
        "contract": "ym_sprint91_wc3_new_math_audit",
        "complete": False,
        "route_decision": route_decision,
        "receipt_path": RECEIPT_PATH,
        "receipt_present": receipt_present,
        "theorem_table": "ym_sprint91_wc3_new_math_theorem_table.csv",
        "gate_table": "ym_sprint91_wc3_new_math_gate_table.csv",
        "expected_theorem_ids": ["T1", "T2", "T3", "T4", "T5"],
        "expected_theorem_anchors": expected_theorem_anchors,
        "present_theorem_anchors": present_theorem_anchors,
        "theorem_list_t1_to_t5_present": theorem_list_present,
        "t1_cauchy_schwarz_contraction_closed_conditionally": (
            t1_closed_conditionally
        ),
        "master_condition_open": master_condition_open,
        "wc3_derived": wc3_derived,
        "wc3_derived_false": wc3_derived_false and not wc3_derived,
        "clay_yang_mills_promoted": clay_promoted,
        "clay_promotion_recorded_false": clay_promoted_false and not clay_promoted,
        "next_required_gate": "MasterCondition",
        "remaining_blocker": (
            "Sprint 91 WC3 new-math receipt is fail-closed: T1 may be closed "
            "conditionally, but the master condition remains open, WC3 is not "
            "derived, and Clay promotion stays false."
        ),
    }


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    summary = summary_payload(args.repo_root)
    text = receipt_text(args.repo_root)
    route_decision = summary["route_decision"]

    write_csv(
        args.out_dir / "ym_sprint91_wc3_new_math_theorem_table.csv",
        THEOREM_FIELDS,
        theorem_rows(text, route_decision),
    )
    write_csv(
        args.out_dir / "ym_sprint91_wc3_new_math_gate_table.csv",
        GATE_FIELDS,
        gate_rows(
            text=text,
            route_decision=route_decision,
            t1_closed_conditionally=summary[
                "t1_cauchy_schwarz_contraction_closed_conditionally"
            ],
            master_condition_open=summary["master_condition_open"],
            wc3_derived_false=summary["wc3_derived_false"],
            clay_promoted_false=summary["clay_promotion_recorded_false"],
            theorem_list_present=summary["theorem_list_t1_to_t5_present"],
        ),
    )
    (args.out_dir / "ym_sprint91_wc3_new_math_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
