#!/usr/bin/env python3
"""Boundary-delta1 lower-bound telemetry on raw N128 data."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import ns_alignment_gap_bin_scan as gap_scan


SCRIPT_NAME = "scripts/ns_boundary_delta1_uniformity_scan.py"
CONTRACT = "ns_boundary_delta1_uniformity_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_DELTA1_UNIFORMITY_SCAN"
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_boundary_delta1_uniformity_scan_N128_20260621.json"
)
DEFAULT_THRESHOLD_VALUES = (0.5, 1.0, 2.0, 4.0, 8.0)
DEFAULT_BAND_VALUES = (0.01, 0.05, 0.10, 0.20)
OK_STATUS = "ok"
ERROR_STATUS = "error"
PARTIAL_STATUS = "partial"

CONTROL_CARD = {
    "O": "Scan raw N128 flow for boundary-delta1 lower-bound telemetry.",
    "R": (
        "Approximate dOmega_K by small-|lambda2| bands, compute delta1=|lambda1| and strain norms there, "
        "test the exact operator/Frobenius boundary identities numerically, and bin minima/quantiles by delta1 thresholds."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed: malformed archive, non-finite fields, or arithmetic mismatches become explicit errors.",
    "L": "Emit per-frame and aggregate telemetry on boundary bands, delta1 thresholds, identity residuals, and normalized lower-bound proxies.",
    "P": ROUTE_DECISION,
    "G": "Empirical scan only; no theorem, closure, or Clay promotion.",
    "F": "Boundary is approximated by finite |lambda2| bands and all lower bounds remain telemetry rather than proof.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=gap_scan.DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--frame", type=gap_scan._nonnegative_int, default=None)
    parser.add_argument("--max-frames", type=gap_scan._positive_int, default=None)
    parser.add_argument("--threshold", type=float, nargs="*", default=list(DEFAULT_THRESHOLD_VALUES))
    parser.add_argument("--band-eps", type=float, nargs="*", default=list(DEFAULT_BAND_VALUES))
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _quantile_map(values: np.ndarray) -> dict[str, float]:
    if values.size == 0:
        return {"p05": 0.0, "p25": 0.0, "p50": 0.0, "p75": 0.0, "p95": 0.0}
    return {
        "p05": float(np.quantile(values, 0.05)),
        "p25": float(np.quantile(values, 0.25)),
        "p50": float(np.quantile(values, 0.50)),
        "p75": float(np.quantile(values, 0.75)),
        "p95": float(np.quantile(values, 0.95)),
    }


def _frame_row(
    frame_slot: int,
    snapshot: int,
    bundle: gap_scan.RawBundle,
    thresholds: list[float],
    band_values: list[float],
    warnings: list[str],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(frame_slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
    }
    try:
        u, v, w = gap_scan._raw_velocity_frame(bundle, snapshot)
        lambda1, lambda2, lambda3, _e1, _e3, _ox, _oy, _oz, _omega_norm_sq = (
            gap_scan._strain_and_vorticity_from_velocity(u, v, w, bundle.domain_length)
        )
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [str(exc)]
        return ERROR_STATUS, row

    finite = np.isfinite(lambda1) & np.isfinite(lambda2) & np.isfinite(lambda3)
    if not np.any(finite):
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite cells"]
        return ERROR_STATUS, row

    lambda1_f = np.asarray(lambda1[finite], dtype=np.float64)
    lambda2_f = np.asarray(lambda2[finite], dtype=np.float64)
    lambda3_f = np.asarray(lambda3[finite], dtype=np.float64)
    delta1_f = np.abs(lambda1_f)
    operator_f = np.maximum(np.abs(lambda1_f), np.maximum(np.abs(lambda2_f), np.abs(lambda3_f)))
    frob_f = np.sqrt(np.maximum(0.0, lambda1_f * lambda1_f + lambda2_f * lambda2_f + lambda3_f * lambda3_f))
    velocity_rms = float(
        math.sqrt(np.mean(np.asarray(u, dtype=np.float64) ** 2 + np.asarray(v, dtype=np.float64) ** 2 + np.asarray(w, dtype=np.float64) ** 2))
    )
    global_strain_max = float(np.max(frob_f))
    row["finite_cell_count"] = int(delta1_f.size)
    row["global_strain_frob_max"] = global_strain_max
    row["velocity_rms"] = velocity_rms

    boundary_band_rows: list[dict[str, Any]] = []
    for band_eps in band_values:
        boundary_mask = np.abs(lambda2_f) <= float(band_eps)
        band_delta1 = delta1_f[boundary_mask]
        band_operator = operator_f[boundary_mask]
        band_frob = frob_f[boundary_mask]
        boundary_count = int(band_delta1.size)
        band_row: dict[str, Any] = {
            "band_eps": float(band_eps),
            "boundary_count": boundary_count,
            "boundary_fraction": gap_scan._fraction(boundary_count, int(delta1_f.size)),
            "operator_delta1_residual_max": 0.0 if boundary_count == 0 else float(np.max(np.abs(band_operator - band_delta1))),
            "frob_delta1_residual_max": 0.0 if boundary_count == 0 else float(np.max(np.abs((band_frob / math.sqrt(2.0)) - band_delta1))),
            "gap_threshold_rows": [],
        }
        for threshold in thresholds:
            active = band_delta1 >= float(threshold)
            active_delta1 = band_delta1[active]
            if active_delta1.size == 0:
                band_row["gap_threshold_rows"].append(
                    {
                        "delta1_threshold": float(threshold),
                        "active_count": 0,
                        "active_fraction_of_boundary": 0.0,
                        "boundary_gap_separation": 0.0,
                        "delta1_min": 0.0,
                        "delta1_quantiles": _quantile_map(np.asarray([], dtype=np.float64)),
                    }
                )
                continue
            band_row["gap_threshold_rows"].append(
                {
                    "delta1_threshold": float(threshold),
                    "active_count": int(active_delta1.size),
                    "active_fraction_of_boundary": gap_scan._fraction(int(active_delta1.size), boundary_count),
                    "boundary_gap_separation": float(np.min(active_delta1) / global_strain_max) if global_strain_max > 0.0 else 0.0,
                    "delta1_min": float(np.min(active_delta1)),
                    "delta1_quantiles": _quantile_map(active_delta1),
                    "velocity_rms_ratio_min": float(np.min(active_delta1) / velocity_rms) if velocity_rms > 0.0 else 0.0,
                }
            )
        boundary_band_rows.append(band_row)

    row["boundary_band_rows"] = boundary_band_rows
    row["status"] = OK_STATUS
    if warnings:
        row["warnings"] = list(warnings)
    return OK_STATUS, row


def _aggregate(frame_rows: list[dict[str, Any]], thresholds: list[float], band_values: list[float]) -> dict[str, Any]:
    ok_rows = [row for row in frame_rows if row.get("status") == OK_STATUS]
    aggregate: dict[str, Any] = {
        "processed_frames": len(frame_rows),
        "ok_frames": len(ok_rows),
        "status_counts": {},
        "band_rows": [],
    }
    for row in frame_rows:
        status = str(row.get("status", ERROR_STATUS))
        aggregate["status_counts"][status] = int(aggregate["status_counts"].get(status, 0)) + 1
    if not ok_rows:
        return aggregate

    finite_total = sum(int(row["finite_cell_count"]) for row in ok_rows)
    aggregate["finite_cell_count"] = finite_total
    aggregate["global_strain_frob_max"] = max(float(row["global_strain_frob_max"]) for row in ok_rows)
    aggregate["velocity_rms_mean"] = sum(float(row["velocity_rms"]) for row in ok_rows) / len(ok_rows)

    for band_eps in band_values:
        band_rows = [
            next((entry for entry in row["boundary_band_rows"] if math.isclose(entry["band_eps"], float(band_eps))), None)
            for row in ok_rows
        ]
        boundary_total = sum(int(entry["boundary_count"]) for entry in band_rows if entry)
        agg_band: dict[str, Any] = {
            "band_eps": float(band_eps),
            "boundary_count": boundary_total,
            "boundary_fraction": gap_scan._fraction(boundary_total, finite_total),
            "gap_threshold_rows": [],
        }
        for threshold in thresholds:
            active_total = 0
            mins: list[float] = []
            gaps: list[float] = []
            q05s: list[float] = []
            q25s: list[float] = []
            q50s: list[float] = []
            q75s: list[float] = []
            q95s: list[float] = []
            for band_row in band_rows:
                if not band_row:
                    continue
                threshold_row = next(
                    (entry for entry in band_row["gap_threshold_rows"] if math.isclose(entry["delta1_threshold"], float(threshold))),
                    None,
                )
                if not threshold_row:
                    continue
                active_total += int(threshold_row["active_count"])
                if threshold_row["active_count"] > 0:
                    mins.append(float(threshold_row["delta1_min"]))
                    gaps.append(float(threshold_row["boundary_gap_separation"]))
                    quantiles = threshold_row["delta1_quantiles"]
                    q05s.append(float(quantiles["p05"]))
                    q25s.append(float(quantiles["p25"]))
                    q50s.append(float(quantiles["p50"]))
                    q75s.append(float(quantiles["p75"]))
                    q95s.append(float(quantiles["p95"]))
            agg_band["gap_threshold_rows"].append(
                {
                    "delta1_threshold": float(threshold),
                    "active_count": active_total,
                    "active_fraction_of_boundary": gap_scan._fraction(active_total, boundary_total),
                    "boundary_gap_separation": 0.0 if not gaps else float(sum(gaps) / len(gaps)),
                    "delta1_min": 0.0 if not mins else float(min(mins)),
                    "delta1_quantiles": {
                        "p05": 0.0 if not q05s else float(sum(q05s) / len(q05s)),
                        "p25": 0.0 if not q25s else float(sum(q25s) / len(q25s)),
                        "p50": 0.0 if not q50s else float(sum(q50s) / len(q50s)),
                        "p75": 0.0 if not q75s else float(sum(q75s) / len(q75s)),
                        "p95": 0.0 if not q95s else float(sum(q95s) / len(q95s)),
                    },
                }
            )
        aggregate["band_rows"].append(agg_band)

    gap_threshold_rows: list[dict[str, Any]] = []
    if aggregate["band_rows"]:
        reference_band = min(aggregate["band_rows"], key=lambda row: float(row["band_eps"]))
        for threshold_row in reference_band["gap_threshold_rows"]:
            gap_threshold_rows.append(dict(threshold_row, band_eps=float(reference_band["band_eps"])))
    aggregate["gap_threshold_rows"] = gap_threshold_rows
    return aggregate


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "script": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "authority": gap_scan._authority(),
        "status": OK_STATUS,
        "raw_archive": str(args.raw_archive),
    }
    try:
        bundle = gap_scan._load_raw_bundle(Path(args.raw_archive), warnings)
        frame_count = int(bundle.frame_count)
        if args.frame is not None:
            snapshots = [int(args.frame)]
        else:
            snapshots = list(range(frame_count))
            if args.max_frames is not None:
                snapshots = snapshots[: int(args.max_frames)]
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [str(exc)]
        output.write_text(gap_scan._json_text(payload, args.pretty), encoding="utf-8")
        return 1

    thresholds = gap_scan._parse_thresholds(list(args.threshold))
    band_values = gap_scan._parse_thresholds(list(args.band_eps))

    frame_rows: list[dict[str, Any]] = []
    status_counts: dict[str, int] = {}
    for slot, snapshot in enumerate(snapshots):
        frame_warnings = list(warnings)
        status, row = _frame_row(slot, int(snapshot), bundle, thresholds, band_values, frame_warnings)
        frame_rows.append(row)
        status_counts[status] = status_counts.get(status, 0) + 1

    aggregate = _aggregate(frame_rows, thresholds, band_values)
    payload["frame_rows"] = frame_rows
    payload["aggregate"] = aggregate
    payload["parameters"] = {
        "delta1_thresholds": [float(value) for value in thresholds],
        "band_eps_values": [float(value) for value in band_values],
        "requested_frame_count": len(snapshots),
    }
    payload["warnings"] = warnings
    payload["status_counts"] = status_counts
    if status_counts.get(ERROR_STATUS, 0) > 0:
        payload["status"] = PARTIAL_STATUS if status_counts.get(OK_STATUS, 0) > 0 else ERROR_STATUS
    output.write_text(gap_scan._json_text(payload, args.pretty), encoding="utf-8")
    return 0 if payload["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
