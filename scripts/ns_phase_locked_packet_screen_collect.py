#!/usr/bin/env python3
"""Collect partial cyclic-packet screen results without upgrading their authority.

The collector reads endpoint JSON files produced by
``ns_phase_locked_packet_search.py`` and ranks them by actual moving-packet
survival.  It also retains a small nondominated telemetry frontier and best
rows per allocation/helicity seed, so a quarter-window batch cannot silently
collapse into one static family before half-window inspection.

This is empirical bookkeeping only.  It neither validates a recurrence
mechanism nor supplies an NS estimate.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_phase_locked_packet_screen_collect.py"
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_phase_locked_packet_quarter_collection_N32_20260716.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, action="append", default=[],
                        help="endpoint JSON file; may be supplied repeatedly")
    parser.add_argument("--input-directory", type=Path, default=None,
                        help="directory recursively scanned for endpoint JSON files")
    parser.add_argument("--glob", default="quarter_*.json")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--top", type=int, default=16)
    return parser.parse_args()


def authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def finite(value: Any, fallback: float) -> float:
    try:
        number = float(value)
    except (TypeError, ValueError):
        return fallback
    return number if math.isfinite(number) else fallback


def source_paths(args: argparse.Namespace) -> list[Path]:
    paths = list(args.input)
    if args.input_directory is not None:
        paths.extend(sorted(args.input_directory.rglob(args.glob)))
    unique = sorted({path.resolve() for path in paths})
    if not unique:
        raise ValueError("provide at least one --input or --input-directory containing endpoint JSON files")
    return unique


def row_from_payload(path: Path, payload: dict[str, Any]) -> dict[str, Any] | None:
    endpoints = payload.get("endpoint_evolutions", [])
    if not endpoints:
        return None
    endpoint_row = endpoints[0]
    endpoint = endpoint_row.get("endpoint", {})
    ledger = endpoint.get("designed_role_transfer", {})
    capture = ledger.get("target_dynamics_capture", {})
    topology = payload.get("topology", {})
    seed = topology.get("selected_helicity_seed", {})
    inputs = payload.get("inputs", {})
    return {
        "path": str(path),
        "allocation": inputs.get("role_shares"),
        "helicity_static_rank": seed.get("rank"),
        "phase_sample_index": inputs.get("phase_sample_index"),
        "seed": inputs.get("seed"),
        "moving_packet_recurrence_ratio": finite(endpoint.get("moving_packet_recurrence_ratio"), -math.inf),
        "moving_packet_heat_compensated_ratio": finite(endpoint.get("moving_packet_heat_compensated_ratio"), -math.inf),
        "min_moving_window_recurrence_ratio": finite(endpoint.get("min_moving_window_recurrence_ratio"), -math.inf),
        "moving_packet_scale_displacement": endpoint.get("moving_packet_scale_displacement"),
        "negative_over_viscous": finite(endpoint.get("nonlinear_negative_over_viscous_loss"), math.inf),
        "positive_over_viscous": finite(endpoint.get("nonlinear_positive_over_viscous_loss"), -math.inf),
        "intended_loop_balance": finite(ledger.get("intended_loop_balance"), -math.inf),
        "feedback_loop_closure_fraction": finite(ledger.get("feedback_loop_closure_fraction"), -math.inf),
        "target_dynamics_capture": finite(capture.get("designed_over_full_absolute_activity"), -math.inf),
        "designed_conservation_residual": finite(ledger.get("max_checkpoint_conservation_residual"), math.inf),
        "support_leakage_fraction": finite(
            endpoint.get("window_checkpoints", [{}])[-1].get("support_leakage_fraction"), math.inf
        ),
    }


def dominates(left: dict[str, Any], right: dict[str, Any]) -> bool:
    """Conservative diagnostic Pareto dominance; endpoint survival is included.

    This frontier is for preserving candidates for inspection, not automatic
    scientific selection.  Higher is better except negative transfer and
    support leakage, where lower is better.
    """
    maximize = (
        "moving_packet_recurrence_ratio",
        "moving_packet_heat_compensated_ratio",
        "intended_loop_balance",
        "target_dynamics_capture",
    )
    minimize = ("negative_over_viscous", "support_leakage_fraction")
    no_worse = all(left[key] >= right[key] for key in maximize) and all(
        left[key] <= right[key] for key in minimize
    )
    strictly_better = any(left[key] > right[key] for key in maximize) or any(
        left[key] < right[key] for key in minimize
    )
    return no_worse and strictly_better


def best_by(rows: list[dict[str, Any]], key_name: str) -> list[dict[str, Any]]:
    grouped: dict[str, dict[str, Any]] = {}
    for row in rows:
        key = json.dumps(row.get(key_name), sort_keys=True)
        current = grouped.get(key)
        if current is None or row["moving_packet_recurrence_ratio"] > current["moving_packet_recurrence_ratio"]:
            grouped[key] = row
    return sorted(grouped.values(), key=lambda row: row["moving_packet_recurrence_ratio"], reverse=True)


def main() -> None:
    args = parse_args()
    if args.top <= 0:
        raise ValueError("--top must be positive")
    rows: list[dict[str, Any]] = []
    skipped: list[dict[str, str]] = []
    for path in source_paths(args):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            skipped.append({"path": str(path), "reason": str(error)})
            continue
        row = row_from_payload(path, payload)
        if row is None:
            skipped.append({"path": str(path), "reason": "no endpoint_evolutions; task may be planned or static-only"})
        else:
            rows.append(row)
    if not rows:
        raise ValueError("no completed endpoint payloads were found")
    ranked = sorted(rows, key=lambda row: row["moving_packet_recurrence_ratio"], reverse=True)
    frontier = [
        row for row in ranked
        if not any(other is not row and dominates(other, row) for other in ranked)
    ]
    payload = {
        "contract": "ns_phase_locked_packet_partial_screen_collection",
        "authority": authority(),
        "status": "partial_empirical_collection",
        "completed_task_count": len(rows),
        "skipped_inputs": skipped,
        "primary_ranking": "descending moving_packet_recurrence_ratio",
        "top_by_endpoint_survival": ranked[:args.top],
        "diagnostic_pareto_frontier": frontier[:args.top],
        "best_per_role_allocation": best_by(rows, "allocation"),
        "best_per_helicity_seed": best_by(rows, "helicity_static_rank"),
        "interpretation": (
            "Use endpoint survival as the main promotion signal. The Pareto frontier, designed-loop telemetry, "
            "and target dynamics capture preserve competing mechanisms for later inspection; none proves a "
            "packet barrier or Navier--Stokes estimate."
        ),
        "next_selection_protocol": [
            "Inspect leading rows and retain allocation/helicity diversity before scheduling half windows.",
            "Reject a task only with its declared admissibility and capture telemetry in view.",
            "Do not infer full-convolution source attribution from the designed-triad throughput convention.",
        ],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
