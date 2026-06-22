#!/usr/bin/env python3
"""Normalize amplitude-weighted K_N(A) profile telemetry into a fail-closed surface."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/ns_triad_amplitude_weighted_negative_frame_scan.py"
CONTRACT = "ns_triad_amplitude_weighted_negative_frame_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_AMPLITUDE_WEIGHTED_NEGATIVE_FRAME_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_INPUT_CSV = Path("/home/c/Downloads/wall1_amplitude_profiles.csv")
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_amplitude_weighted_negative_frame_scan_N128_20260623.json"
)

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "promoted": False,
}

FRAME_COERCIVE_THRESHOLD = 0.25
HIGH_DISSIPATION_THRESHOLD = 5.0
LOW_BAND_PROFILE_KEYS = ("low-k", "low k", "low_k", "lowband")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-csv", type=Path, default=DEFAULT_INPUT_CSV)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _safe_float(value: Any) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"non-finite value: {value!r}")
    return parsed


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values)) if values else 0.0


def _profile_branch(profile: str, lmin: float, dissipation: float) -> str:
    lowered = profile.lower()
    if lmin >= FRAME_COERCIVE_THRESHOLD:
        return "frame-coercive"
    if any(key in lowered for key in LOW_BAND_PROFILE_KEYS):
        return "low-band"
    if dissipation > HIGH_DISSIPATION_THRESHOLD:
        return "high-dissipation"
    return "unclassified"


def main() -> int:
    args = _parse_args()
    rows: list[dict[str, Any]] = []
    with args.input_csv.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for index, source_row in enumerate(reader):
            profile = str(source_row["profile"]).strip()
            lmin = _safe_float(source_row["lmin"])
            lmax = _safe_float(source_row["lmax"])
            pi_frac = _safe_float(source_row["pi_frac"])
            dissipation = _safe_float(source_row["dissipation"])
            branch = _profile_branch(profile, lmin, dissipation)
            rows.append(
                {
                    "row_index": index,
                    "profile": profile,
                    "lambda_min_kn_a": lmin,
                    "lambda_max_kn_a": lmax,
                    "psi_pi_fraction": pi_frac,
                    "dissipation_proxy": dissipation,
                    "branch_candidate": branch,
                    "frame_coercive": lmin >= FRAME_COERCIVE_THRESHOLD,
                    "low_band_escape_candidate": branch == "low-band",
                    "high_dissipation_escape_candidate": branch == "high-dissipation",
                    "candidate_only": True,
                    "fail_closed": True,
                    "theorem_promoted": False,
                    "full_ns_promoted": False,
                    "clay_promoted": False,
                    "status": "ok",
                }
            )

    lmins = [row["lambda_min_kn_a"] for row in rows]
    lmaxs = [row["lambda_max_kn_a"] for row in rows]
    dissipations = [row["dissipation_proxy"] for row in rows]
    pi_fracs = [row["psi_pi_fraction"] for row in rows]
    frame_count = sum(1 for row in rows if row["frame_coercive"])
    low_band_count = sum(1 for row in rows if row["low_band_escape_candidate"])
    high_diss_count = sum(1 for row in rows if row["high_dissipation_escape_candidate"])
    unclassified_count = sum(1 for row in rows if row["branch_candidate"] == "unclassified")
    worst_row = min(rows, key=lambda row: row["lambda_min_kn_a"]) if rows else None

    aggregate = {
        "status": "ok",
        "candidate_only": True,
        "fail_closed": True,
        "profile_count": len(rows),
        "lambda_min_kn_a_mean": _mean(lmins),
        "lambda_min_kn_a_min": min(lmins, default=0.0),
        "lambda_min_kn_a_max": max(lmins, default=0.0),
        "lambda_max_kn_a_mean": _mean(lmaxs),
        "lambda_max_kn_a_max": max(lmaxs, default=0.0),
        "psi_pi_fraction_mean": _mean(pi_fracs),
        "dissipation_proxy_mean": _mean(dissipations),
        "dissipation_proxy_min": min(dissipations, default=0.0),
        "dissipation_proxy_max": max(dissipations, default=0.0),
        "frame_coercive_profile_count": frame_count,
        "low_band_escape_profile_count": low_band_count,
        "high_dissipation_escape_profile_count": high_diss_count,
        "unclassified_profile_count": unclassified_count,
        "worst_profile_name": worst_row["profile"] if worst_row else None,
        "worst_profile_lambda_min_kn_a": worst_row["lambda_min_kn_a"] if worst_row else 0.0,
        "amplitude_weighted_negative_frame_status": "fail-closed",
        "amplitude_weighted_negative_frame_source": "wall1_amplitude_profiles_csv",
        "amplitude_weighted_negative_frame_candidate_only": True,
        "amplitude_weighted_negative_frame_fail_closed": True,
        "amplitude_weighted_negative_frame_theorem_promoted": False,
        "amplitude_weighted_negative_frame_full_ns_promoted": False,
        "amplitude_weighted_negative_frame_clay_promoted": False,
        "wall1a_status": "unproved",
        "wall2_bridge_status": "unproved",
        "frame_coercive_threshold": FRAME_COERCIVE_THRESHOLD,
        "high_dissipation_threshold": HIGH_DISSIPATION_THRESHOLD,
    }

    out = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": "ok",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "input_csv": str(args.input_csv),
        "rows": rows,
        "aggregate": aggregate,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(out, pretty=args.pretty), encoding="utf-8")
    print(_json_text(out, pretty=args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
