#!/usr/bin/env python3
"""Normalize square-wave / harmonic-stack spectral-sharpness telemetry."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/ns_triad_square_wave_stack_scan.py"
CONTRACT = "ns_triad_square_wave_stack_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SPECTRAL_SHARPNESS_SQUARE_WAVE_STACK_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_INPUT_CSV = Path("/home/c/Downloads/wall1_squarewave_fork.csv")
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_spectral_sharpness_square_wave_stack_scan_N128_20260623.json"
)

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "promoted": False,
}

FRAME_FLOOR_THRESHOLD = 0.25
HIGH_BANDWIDTH_THRESHOLD = 1.5
LOW_DISSIPATION_THRESHOLD = 3.0


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


def _safe_float_default(value: Any, default: float) -> float:
    if value in (None, ""):
        return default
    return _safe_float(value)


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values)) if values else 0.0


def _normalize_branch(branch: str) -> str:
    lowered = branch.strip().lower()
    if lowered == "frame-coerc":
        return "frame-coercive"
    if lowered == "high-diss":
        return "high-dissipation"
    return lowered


def main() -> int:
    args = _parse_args()
    rows: list[dict[str, Any]] = []
    if not args.input_csv.exists():
        out = {
            "script_name": SCRIPT_NAME,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "authority": AUTHORITY,
            "status": "error",
            "candidate_only": True,
            "empirical_non_promoting": True,
            "fail_closed": True,
            "input_csv": str(args.input_csv),
            "rows": [],
            "aggregate": {
                "status": "error",
                "candidate_only": True,
                "fail_closed": True,
                "spectral_sharpness_square_wave_stack_status": "fail-closed",
                "spectral_sharpness_square_wave_stack_source": "missing-input",
                "missing_input": True,
                "wall1a_status": "unproved",
                "wall2_status": "unproved",
            },
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(out, pretty=args.pretty), encoding="utf-8")
        print(_json_text(out, pretty=args.pretty))
        return 0

    with args.input_csv.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for index, source_row in enumerate(reader):
            profile = str(source_row["profile"]).strip()
            lmin = _safe_float(source_row["lmin"])
            lmax = _safe_float_default(source_row.get("lmax"), 0.0)
            n_eff = _safe_float(source_row["Neff"])
            dissipation = _safe_float(source_row["D"])
            bkm_proxy = _safe_float(source_row["BKM"])
            branch = _normalize_branch(str(source_row["branch"]))
            triple = str(source_row.get("triple", "False")).strip().lower() == "true"
            product_separation = lmin * bkm_proxy
            rows.append(
                {
                    "row_index": index,
                    "profile": profile,
                    "lambda_min_kn_a": lmin,
                    "lambda_max_kn_a": lmax,
                    "n_eff": n_eff,
                    "dissipation_proxy": dissipation,
                    "bkm_proxy": bkm_proxy,
                    "branch": branch,
                    "triple_danger": triple,
                    "product_separation_lambda_min_times_bkm_proxy": product_separation,
                    "low_frame_floor": lmin < FRAME_FLOOR_THRESHOLD,
                    "high_bandwidth": n_eff > HIGH_BANDWIDTH_THRESHOLD,
                    "low_dissipation": dissipation < LOW_DISSIPATION_THRESHOLD,
                    "candidate_only": True,
                    "fail_closed": True,
                    "theorem_promoted": False,
                    "full_ns_promoted": False,
                    "clay_promoted": False,
                    "status": "ok",
                }
            )

    lmins = [row["lambda_min_kn_a"] for row in rows]
    neffs = [row["n_eff"] for row in rows]
    dissipations = [row["dissipation_proxy"] for row in rows]
    bkms = [row["bkm_proxy"] for row in rows]
    products = [row["product_separation_lambda_min_times_bkm_proxy"] for row in rows]
    triple_count = sum(1 for row in rows if row["triple_danger"])
    branch_counts = {
        "frame-coercive": sum(1 for row in rows if row["branch"] == "frame-coercive"),
        "low-band": sum(1 for row in rows if row["branch"] == "low-band"),
        "high-dissipation": sum(1 for row in rows if row["branch"] == "high-dissipation"),
    }
    worst_row = min(rows, key=lambda row: row["lambda_min_kn_a"]) if rows else None
    aggregate = {
        "status": "ok",
        "candidate_only": True,
        "fail_closed": True,
        "square_wave_profile_count": len(rows),
        "lambda_min_kn_a_mean": _mean(lmins),
        "lambda_min_kn_a_min": min(lmins, default=0.0),
        "lambda_min_kn_a_max": max(lmins, default=0.0),
        "n_eff_mean": _mean(neffs),
        "dissipation_proxy_mean": _mean(dissipations),
        "bkm_proxy_mean": _mean(bkms),
        "product_separation_lambda_min_times_bkm_proxy_mean": _mean(products),
        "product_separation_lambda_min_times_bkm_proxy_min": min(products, default=0.0),
        "frame_coercive_count": branch_counts["frame-coercive"],
        "low_band_escape_count": branch_counts["low-band"],
        "high_dissipation_escape_count": branch_counts["high-dissipation"],
        "triple_danger_count": triple_count,
        "no_triple_danger": triple_count == 0,
        "all_profiles_classified_safe": triple_count == 0,
        "worst_profile_name": worst_row["profile"] if worst_row else None,
        "worst_profile_lambda_min_kn_a": worst_row["lambda_min_kn_a"] if worst_row else 0.0,
        "worst_profile_branch": worst_row["branch"] if worst_row else None,
        "spectral_sharpness_square_wave_stack_status": "fail-closed",
        "spectral_sharpness_square_wave_stack_source": "wall1_squarewave_fork_csv",
        "spectral_sharpness_square_wave_stack_candidate_only": True,
        "spectral_sharpness_square_wave_stack_fail_closed": True,
        "spectral_sharpness_square_wave_stack_theorem_promoted": False,
        "spectral_sharpness_square_wave_stack_full_ns_promoted": False,
        "spectral_sharpness_square_wave_stack_clay_promoted": False,
        "wall1a_status": "unproved",
        "wall2_status": "unproved",
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
