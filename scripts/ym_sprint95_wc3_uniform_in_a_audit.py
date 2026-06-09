#!/usr/bin/env python3
"""Sprint 95 WC3 uniform-in-a audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734
ETA_BLOCKED_L2 = 4


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint95_wc3_uniform_in_a"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    eta4_q = ETA_BLOCKED_L2 * Q_CURRENT
    return {
        "sprint": 95,
        "uniform_bound_for_all_a_required": True,
        "blocked_l2_eta": ETA_BLOCKED_L2,
        "q_current": Q_CURRENT,
        "eta4_q": eta4_q,
        "eta4_kp_arithmetic_closes": eta4_q < 1.0,
        "eta4_margin": 1.0 - eta4_q,
        "wc3_uniform_in_a_closed_in_repo": True,
        "uniform_connected_schwinger_decay_derived_in_repo": False,
        "continuum_limit_mass_gap_derived_in_repo": False,
        "clay_yang_mills_promoted": False,
        "remaining_open_lemmas": [
            "UniformConnectedSchwingerDecay",
            "ContinuumLimitMassGap",
            "Nontrivial4DSU3YangMillsMeasure",
            "ClayStatementBoundaryDischarged",
            "ExternalAcceptanceToken",
        ],
        "route_decision": "SPRINT95_CLOSES_WC3_UNIFORM_IN_A_ONLY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint95_wc3_uniform_in_a_summary.json").write_text(
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
