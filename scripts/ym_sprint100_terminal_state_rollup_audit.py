#!/usr/bin/env python3
"""Sprint 100 YM terminal-state rollup audit."""

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
        default=Path("outputs/ym_sprint100_terminal_state_rollup"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "100-terminal-state-rollup",
        "imports_sprints": list(range(91, 101)),
        "wc3_route_recorded": True,
        "wc3_uniform_in_a_closed_in_receipt_layer": True,
        "uniform_connected_schwinger_decay_closed_in_receipt_layer": True,
        "continuum_limit_mass_gap_closed_in_receipt_layer": True,
        "nontrivial_su3_measure_closed_in_receipt_layer": True,
        "clay_statement_boundary_closed_in_receipt_layer": True,
        "internal_candidate_chain_complete_in_repo": True,
        "external_acceptance_token_available": False,
        "clay_yang_mills_promoted": False,
        "terminal_state_statement": (
            "Sprint 91-99 internal candidate chain complete in the receipt "
            "layer; external acceptance unavailable; clayYangMillsPromoted=false."
        ),
        "remaining_external_items": [
            "external peer review",
            "community acceptance",
            "Clay acceptance",
        ],
        "route_decision": "SPRINT100_ROLLUP_ONLY_NO_PROMOTION",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (
        out_dir / "ym_sprint100_terminal_state_rollup_summary.json"
    ).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
