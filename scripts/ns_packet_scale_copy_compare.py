#!/usr/bin/env python3
"""Compare non-promoting packet receipts across dyadic finite carriers."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("receipts", nargs="+", type=Path)
    parser.add_argument("--output-json", type=Path)
    return parser.parse_args()


def extract(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text())
    endpoint = payload["endpoint_evolutions"][0]["endpoint"]
    role = endpoint["designed_role_transfer"]
    initial = endpoint["history"][0]
    initial_viscous_rate = 2.0 * payload["inputs"]["nu"] * initial["target_dissipation"]
    return {
        "receipt": str(path),
        "n": payload["inputs"]["n"],
        "target_shell": payload["inputs"]["target_shell"],
        "dt": payload["inputs"]["dt"],
        "actual_time": endpoint["actual_time"],
        "declared_critical_mass": payload["inputs"]["critical_mass"],
        "initial_target_nonlinear_rate": initial["target_nonlinear_rate"],
        "initial_target_dissipation": initial["target_dissipation"],
        "initial_nonlinear_to_viscous_ratio": (
            abs(initial["target_nonlinear_rate"]) / initial_viscous_rate
            if initial_viscous_rate > 0.0 else None
        ),
        "moving_packet_recurrence": endpoint["moving_packet_recurrence_ratio"],
        "fixed_packet_recurrence": endpoint["endpoint_recurrence_ratio"],
        "moving_heat_compensated": endpoint["moving_packet_heat_compensated_ratio"],
        "fixed_heat_compensated": endpoint["endpoint_heat_compensated_ratio"],
        "scale_displacement": endpoint["moving_packet_scale_displacement"],
        "positive_transfer_over_viscous": endpoint["nonlinear_positive_over_viscous_loss"],
        "negative_transfer_over_viscous": endpoint["nonlinear_negative_over_viscous_loss"],
        "designed_target_activity_capture": role["target_dynamics_capture"][
            "designed_over_full_absolute_activity"
        ],
        "intended_loop_balance": role["intended_loop_balance"],
    }


def main() -> None:
    args = parse_args()
    rows = sorted((extract(path) for path in args.receipts), key=lambda row: row["n"])
    transitions = []
    for left, right in zip(rows, rows[1:]):
        transitions.append({
            "from_n": left["n"],
            "to_n": right["n"],
            "moving_recurrence_ratio_of_ratios": (
                right["moving_packet_recurrence"] / left["moving_packet_recurrence"]
            ),
            "fixed_recurrence_ratio_of_ratios": (
                right["fixed_packet_recurrence"] / left["fixed_packet_recurrence"]
            ),
            "moving_heat_compensated_change": (
                right["moving_heat_compensated"] - left["moving_heat_compensated"]
            ),
            "net_transfer_balance_change": (
                (right["positive_transfer_over_viscous"] - right["negative_transfer_over_viscous"])
                - (left["positive_transfer_over_viscous"] - left["negative_transfer_over_viscous"])
            ),
            "initial_nonlinear_to_viscous_ratio_of_ratios": (
                right["initial_nonlinear_to_viscous_ratio"]
                / left["initial_nonlinear_to_viscous_ratio"]
            ),
        })
    report = {
        "contract": "ns_packet_dyadic_scale_copy_nonpromoting_comparison",
        "authority": {
            "empirical_non_promoting": True,
            "theorem_authority": False,
            "clay_authority": False,
        },
        "warning": (
            "two finite periodic carriers do not establish an asymptotic scaling law; the declared "
            "critical-mass normalization is a shell-packet convention, not by itself a continuum "
            "Navier--Stokes scaling theorem"
        ),
        "rows": rows,
        "transitions": transitions,
        "decision": (
            "retention strengthens, but the declared fixed shell-critical mass does not preserve "
            "nonlinear-to-viscous strength; repair the dynamical scaling convention before using "
            "this pair to support or reject a scale-uniform packet contraction"
            if transitions and abs(
                transitions[-1]["initial_nonlinear_to_viscous_ratio_of_ratios"] - 1.0
            ) > 0.10 else
            "the available transition approximately preserves initial nonlinear-to-viscous strength"
        ),
    }
    rendered = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
