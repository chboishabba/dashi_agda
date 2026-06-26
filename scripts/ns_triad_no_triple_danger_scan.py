#!/usr/bin/env python3
"""Normalize no-triple-danger telemetry from the adversarial amplitude sweep."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/ns_triad_no_triple_danger_scan.py"
CONTRACT = "ns_triad_no_triple_danger_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_NO_TRIPLE_DANGER_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_INPUT_CSV = Path("/home/c/Downloads/wall1_fork_adversarial.csv")
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_no_triple_danger_scan_N128_20260623.json"
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
HIGH_BKM_PROXY_THRESHOLD = 3.0
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


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values)) if values else 0.0


def _branch_reason(branch: str, triple_danger: bool) -> str:
    if triple_danger:
        return "forbidden triple-danger conjunction detected"
    if branch == "frame-coercive":
        return f"lambda_min_kn_a >= {FRAME_FLOOR_THRESHOLD:.2f}"
    if branch == "low-band":
        return f"N_eff <= {HIGH_BANDWIDTH_THRESHOLD:.1f}"
    if branch in ("high-dissipation", "high-diss"):
        return f"dissipation >= {LOW_DISSIPATION_THRESHOLD:.1f}"
    return "branch did not certify a canonical safe lane"


def main() -> int:
    args = _parse_args()
    rows: list[dict[str, Any]] = []
    with args.input_csv.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for index, source_row in enumerate(reader):
            alpha = _safe_float(source_row["alpha"])
            lmin = _safe_float(source_row["lmin"])
            lmax = _safe_float(source_row["lmax"])
            energy = _safe_float(source_row["E"])
            dissipation = _safe_float(source_row["D"])
            n_eff = _safe_float(source_row["Neff"])
            bkm_proxy = _safe_float(source_row["BKMproxy"])
            branch = str(source_row["branch"]).strip()
            low_frame_floor = lmin < FRAME_FLOOR_THRESHOLD
            high_bandwidth = n_eff > HIGH_BANDWIDTH_THRESHOLD
            high_bkm_proxy = bkm_proxy > HIGH_BKM_PROXY_THRESHOLD
            low_dissipation = dissipation < LOW_DISSIPATION_THRESHOLD
            triple_danger = low_frame_floor and high_bandwidth and high_bkm_proxy and low_dissipation
            product_separation = lmin * bkm_proxy
            rows.append(
                {
                    "row_index": index,
                    "alpha": alpha,
                    "lambda_min_kn_a": lmin,
                    "lambda_max_kn_a": lmax,
                    "energy": energy,
                    "dissipation_proxy": dissipation,
                    "n_eff": n_eff,
                    "bkm_proxy": bkm_proxy,
                    "branch": branch,
                    "low_frame_floor": low_frame_floor,
                    "high_bandwidth": high_bandwidth,
                    "high_bkm_proxy": high_bkm_proxy,
                    "low_dissipation": low_dissipation,
                    "triple_danger": triple_danger,
                    "product_separation_lambda_min_times_bkm_proxy": product_separation,
                    "branch_safety_reason": _branch_reason(branch, triple_danger),
                    "frame_floor_threshold": FRAME_FLOOR_THRESHOLD,
                    "high_bandwidth_threshold": HIGH_BANDWIDTH_THRESHOLD,
                    "high_bkm_proxy_threshold": HIGH_BKM_PROXY_THRESHOLD,
                    "low_dissipation_threshold": LOW_DISSIPATION_THRESHOLD,
                    "candidate_only": True,
                    "fail_closed": True,
                    "theorem_promoted": False,
                    "full_ns_promoted": False,
                    "clay_promoted": False,
                    "status": "ok",
                }
            )

    lmins = [row["lambda_min_kn_a"] for row in rows]
    dissipations = [row["dissipation_proxy"] for row in rows]
    n_effs = [row["n_eff"] for row in rows]
    bkm_proxies = [row["bkm_proxy"] for row in rows]
    products = [row["product_separation_lambda_min_times_bkm_proxy"] for row in rows]
    triple_danger_count = sum(1 for row in rows if row["triple_danger"])
    worst_row = min(rows, key=lambda row: row["lambda_min_kn_a"]) if rows else None

    aggregate = {
        "status": "ok",
        "candidate_only": True,
        "fail_closed": True,
        "adversarial_profile_count": len(rows),
        "lambda_min_kn_a_mean": _mean(lmins),
        "lambda_min_kn_a_min": min(lmins, default=0.0),
        "lambda_min_kn_a_max": max(lmins, default=0.0),
        "dissipation_proxy_mean": _mean(dissipations),
        "n_eff_mean": _mean(n_effs),
        "bkm_proxy_mean": _mean(bkm_proxies),
        "triple_danger_count": triple_danger_count,
        "no_triple_danger": triple_danger_count == 0,
        "all_profiles_classified_safe": triple_danger_count == 0,
        "product_separation_lambda_min_times_bkm_proxy_mean": _mean(products),
        "product_separation_lambda_min_times_bkm_proxy_min": min(products, default=0.0),
        "product_separation_lambda_min_times_bkm_proxy_max": max(products, default=0.0),
        "worst_row_alpha": worst_row["alpha"] if worst_row else 0.0,
        "worst_row_branch": worst_row["branch"] if worst_row else None,
        "worst_row_lambda_min_kn_a": worst_row["lambda_min_kn_a"] if worst_row else 0.0,
        "worst_row_n_eff": worst_row["n_eff"] if worst_row else 0.0,
        "worst_row_bkm_proxy": worst_row["bkm_proxy"] if worst_row else 0.0,
        "worst_row_dissipation_proxy": worst_row["dissipation_proxy"] if worst_row else 0.0,
        "no_triple_danger_status": "fail-closed",
        "no_triple_danger_source": "wall1_fork_adversarial_csv",
        "no_triple_danger_candidate_only": True,
        "no_triple_danger_fail_closed": True,
        "no_triple_danger_theorem_promoted": False,
        "no_triple_danger_full_ns_promoted": False,
        "no_triple_danger_clay_promoted": False,
        "wall1a_status": "unproved",
        "wall2_status": "unproved",
        "frame_floor_threshold": FRAME_FLOOR_THRESHOLD,
        "high_bandwidth_threshold": HIGH_BANDWIDTH_THRESHOLD,
        "high_bkm_proxy_threshold": HIGH_BKM_PROXY_THRESHOLD,
        "low_dissipation_threshold": LOW_DISSIPATION_THRESHOLD,
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
