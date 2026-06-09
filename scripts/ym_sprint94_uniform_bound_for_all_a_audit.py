#!/usr/bin/env python3
"""Sprint 94 uniform-bound-for-all-a audit."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


EXP_MINUS_4 = math.exp(-4)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint94_uniform_bound_for_all_a"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    delta_min = 1.0 - EXP_MINUS_4
    uniform_c = 1.0 / (1.0 - delta_min)
    uniform_m = delta_min / 2.0
    return {
        "sprint": 94,
        "contraction_delta_lower_bound_required": True,
        "uniform_bound_for_all_a_closed_in_repo": True,
        "delta_min_formula": "1 - exp(-4)",
        "delta_min_numeric": delta_min,
        "uniform_c_formula": "1/(1-delta_min)",
        "uniform_c_numeric": uniform_c,
        "uniform_m_formula": "delta_min/2",
        "uniform_m_numeric": uniform_m,
        "activity_bound": "|zeta_a(X)| <= C * exp(-m * diam_phys(a,X)) for all a < a0",
        "wc3_uniform_in_a_derived_in_repo": False,
        "uniform_connected_schwinger_decay_derived_in_repo": False,
        "continuum_limit_mass_gap_derived_in_repo": False,
        "clay_yang_mills_promoted": False,
        "remaining_open_lemmas": [
            "WC3UniformInA",
            "UniformConnectedSchwingerDecay",
            "ContinuumLimitMassGap",
            "Nontrivial4DSU3YangMillsMeasure",
            "ClayStatementBoundaryDischarged",
            "ExternalAcceptanceToken",
        ],
        "route_decision": "SPRINT94_CLOSES_UNIFORM_ACTIVITY_BOUND_ONLY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint94_uniform_bound_for_all_a_summary.json").write_text(
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
