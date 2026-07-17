#!/usr/bin/env python3
"""Collect candidate-only normalized-profile receipts into a quotient atlas.

The report deliberately keeps static profile shape, chi matching, finite
Galerkin packet survival, and coarse interaction turnover separate.  It ranks
neither a theorem nor a preferred profile; it only makes incomplete or
incomparable receipts visible before a profile-uniform claim is attempted.
"""

from __future__ import annotations

import argparse
import glob
import json
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipts", nargs="+", help="JSON paths or glob patterns")
    parser.add_argument("--output-json", type=Path)
    return parser.parse_args()


def expand(patterns: list[str]) -> list[Path]:
    paths: set[Path] = set()
    for pattern in patterns:
        matched = [Path(value) for value in glob.glob(pattern)]
        if matched:
            paths.update(matched)
        else:
            paths.add(Path(pattern))
    return sorted(paths)


def row(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    shape = payload["shape_metrics"]
    static = payload["static_packet_metrics"]
    quotient = payload["quotient_slice"]
    evolution = payload.get("finite_galerkin_evolution")
    result: dict[str, Any] = {
        "receipt": str(path),
        "critical_mass": shape["finite_critical_mass"],
        "chi_absolute": static["chi_absolute"],
        "chi_target": payload["inputs"].get("chi_target"),
        "chi_mismatch": quotient["chi_absolute_mismatch"],
        "chi_matched": quotient["chi_match_within_requested_tolerance"],
        "target_packet_dominance": static["target_packet_dominance"],
        "angular_concentration": shape["angular_second_moment_operator_fraction"],
        "radial_log_width": shape["radial_log_width"],
        "spatial_ipr_fraction": shape["spatial_inverse_participation_fraction"],
        "spatial_entropy_fraction": shape["spatial_shannon_effective_fraction"],
        "evolution_available": evolution is not None,
    }
    if evolution is not None:
        result.update({
            "moving_packet_recurrence_ratio": evolution["moving_packet_recurrence_ratio"],
            "moving_packet_heat_compensated_ratio": evolution["moving_packet_heat_compensated_ratio"],
            "moving_packet_scale_displacement": evolution["moving_packet_scale_displacement"],
            "coarse_interaction_hellinger_squared": evolution[
                "coarse_interaction_hellinger_squared_initial_to_endpoint"
            ],
            "actual_window_time": evolution["actual_window_time"],
        })
    return result


def main() -> None:
    args = parse_args()
    rows = []
    missing = []
    rejected = []
    for path in expand(args.receipts):
        if not path.is_file():
            missing.append(str(path))
            continue
        payload = json.loads(path.read_text())
        if payload.get("contract") != "ns_normalized_profile_quotient_audit_nonpromoting":
            rejected.append(str(path))
            continue
        rows.append(row(path, payload))
    comparable = [entry for entry in rows if entry["chi_matched"] is not False and entry["target_packet_dominance"] >= 0.8]
    output = {
        "contract": "ns_normalized_profile_census_nonpromoting_report",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "receipt_count": len(rows),
        "comparable_tight_chi_matched_count": len(comparable),
        "rows": rows,
        "incomparable_or_broad_profile_receipts": [entry["receipt"] for entry in rows if entry not in comparable],
        "missing": missing,
        "rejected_wrong_contract": rejected,
        "warning": (
            "This is an atlas of finite empirical receipts. Comparable means only that the declared chi slice "
            "matched and target-shell dominance was at least .8; it does not establish quotient completeness "
            "or profile-uniform constants."
        ),
    }
    rendered = json.dumps(output, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
