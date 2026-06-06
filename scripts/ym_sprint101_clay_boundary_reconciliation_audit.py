#!/usr/bin/env python3
"""Sprint 101 Clay boundary reconciliation audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint101_clay_boundary_reconciliation"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "101-clay-boundary-reconciliation",
        "sprint100_internal_candidate_chain_complete": True,
        "sprint100_external_acceptance_available": False,
        "legacy_all_providers_derived_in_repo": False,
        "legacy_clay_statement_boundary_discharged": False,
        "legacy_clay_yang_mills_promoted": False,
        "sprint100_clay_yang_mills_promoted": False,
        "reconciliation_statement": (
            "Legacy authority boundary remains fail-closed; Sprint 91-100 "
            "candidate chain is complete only in the receipt layer; both keep "
            "clayYangMillsPromoted=false."
        ),
        "route_decision": "SPRINT101_RECONCILES_BOUNDARIES_NO_PROMOTION",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (
        out_dir / "ym_sprint101_clay_boundary_reconciliation_summary.json"
    ).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
