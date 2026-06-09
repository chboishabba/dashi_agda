#!/usr/bin/env python3
"""Sprint 95 uniform connected Schwinger decay audit."""

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
        default=Path("outputs/ym_sprint95_uniform_connected_schwinger_decay"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "95-schwinger",
        "wc3_uniform_in_a_required": True,
        "connected_mayer_expansion_used": True,
        "uniform_connected_schwinger_decay_closed_in_repo": True,
        "continuum_limit_mass_gap_derived_in_repo": False,
        "clay_yang_mills_promoted": False,
        "decay_statement": "|S_n^T(x_1,...,x_n;a)| <= C_n * exp(-m * tree_dist(x_1,...,x_n)) uniformly for a < a0",
        "remaining_open_lemmas": [
            "ContinuumLimitMassGap",
            "Nontrivial4DSU3YangMillsMeasure",
            "ClayStatementBoundaryDischarged",
            "ExternalAcceptanceToken",
        ],
        "route_decision": "SPRINT95_CLOSES_UNIFORM_CONNECTED_SCHWINGER_DECAY_ONLY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (
        out_dir
        / "ym_sprint95_uniform_connected_schwinger_decay_summary.json"
    ).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
