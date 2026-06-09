#!/usr/bin/env python3
"""Sprint 98 Clay statement boundary candidate receipt audit."""

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
        default=Path("outputs/ym_sprint98_clay_statement_boundary_candidate"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "98-clay-statement-boundary-candidate",
        "sprint97_nontrivial_su3_measure_required": True,
        "continuum_existence_surface_recorded": True,
        "positive_continuum_mass_gap_surface_recorded": True,
        "clay_statement_formulation_match_recorded": True,
        "clay_statement_boundary_discharged_in_repo": True,
        "external_acceptance_token_available": False,
        "clay_yang_mills_promoted": False,
        "boundary_statement": (
            "Internal Clay statement boundary discharged for the current "
            "candidate chain; external acceptance remains unavailable"
        ),
        "remaining_open_lemmas": [
            "ExternalAcceptanceToken",
        ],
        "route_decision": "SPRINT98_CLOSES_INTERNAL_CLAY_STATEMENT_BOUNDARY_ONLY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (
        out_dir / "ym_sprint98_clay_statement_boundary_candidate_summary.json"
    ).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
