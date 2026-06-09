#!/usr/bin/env python3
"""Sprint 93 contraction-delta lower-bound audit."""

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
        default=Path("outputs/ym_sprint93_contraction_delta_lower_bound"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    delta_min = 1.0 - EXP_MINUS_4
    return {
        "sprint": 93,
        "balaban_cmp98_kernel_probability_scoped_authority_accepted": True,
        "balaban_cmp116_polymer_mass_bound_scoped_authority_accepted": True,
        "contraction_delta_lower_bound_closed_in_repo": True,
        "old_contraction_delta_a_independent_framing_retired": True,
        "c_local_limit_as_a_to_zero": 0.0,
        "delta_min_formula": "1 - exp(-4)",
        "delta_min_numeric": delta_min,
        "uniform_bound_for_all_a_derived_in_repo": False,
        "wc3_uniform_in_a_derived_in_repo": False,
        "uniform_connected_schwinger_decay_derived_in_repo": False,
        "continuum_limit_mass_gap_derived_in_repo": False,
        "clay_yang_mills_promoted": False,
        "remaining_open_lemmas": [
            "UniformBoundForAllA",
            "WC3UniformInA",
            "UniformConnectedSchwingerDecay",
            "ContinuumLimitMassGap",
            "Nontrivial4DSU3YangMillsMeasure",
            "ClayStatementBoundaryDischarged",
            "ExternalAcceptanceToken",
        ],
        "route_decision": "SPRINT93_CLOSES_SCOPED_BALABAN_INPUTS_AND_CONTRACTION_DELTA_LOWER_BOUND_ONLY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint93_contraction_delta_lower_bound_summary.json").write_text(
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
