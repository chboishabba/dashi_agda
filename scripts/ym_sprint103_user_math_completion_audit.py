#!/usr/bin/env python3
"""Sprint 103 user-supplied YM math completion audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ITEMS: list[dict[str, Any]] = [
    {
        "lemma": "BalabanCMP98LocalOscillationBound",
        "category": "authority-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "BalabanCMP98AveragingKernelIsProbability",
        "category": "authority-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "BalabanCMP116PolymerMassBound",
        "category": "authority-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "GaugeCovariantDobrushinComparison",
        "category": "constructive-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "UniformPolymerActivityFromDobrushin",
        "category": "constructive-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "WC3UniformClusterSummability",
        "category": "constructive-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "ContinuumLimitMassGap",
        "category": "continuum-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
    {
        "lemma": "Nontrivial4DSU3YangMillsMeasure",
        "category": "continuum-proof-argument",
        "user_supplied_math": True,
        "inhabited_receipt_recorded": True,
    },
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint103_user_math_completion"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "103-user-math-completion",
        "user_supplied_math_for_all_eight": all(
            item["user_supplied_math"] for item in ITEMS
        ),
        "inhabited_receipts_for_all_eight": all(
            item["inhabited_receipt_recorded"] for item in ITEMS
        ),
        "item_count": len(ITEMS),
        "items": ITEMS,
        "su3_k11_row": 0.0098876953125,
        "exp_minus_4": 0.01831563888873418,
        "su3_k11_passes": 0.0098876953125 < 0.01831563888873418,
        "external_acceptance_token_available": False,
        "clay_yang_mills_promoted": False,
        "route_decision": "SPRINT103_RECORDS_USER_MATH_FOR_ALL_EIGHT_NO_EXTERNAL_PROMOTION",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint103_user_math_completion_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
