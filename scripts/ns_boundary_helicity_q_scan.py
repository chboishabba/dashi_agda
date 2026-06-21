#!/usr/bin/env python3
"""Scan boundary-band helicity/Q telemetry on the raw N128 archive."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import (  # type: ignore
    _frame_indices,
    _frame_pressure,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _pearson,
    _reconstruct_boundary_observables,
)
from ns_pressure_eigenframe_gap_scan import _authority, _spectral_derivative


SCRIPT_NAME = "scripts/ns_boundary_helicity_q_scan.py"
CONTRACT = "ns_boundary_helicity_q_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_HELICITY_Q_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
MISSING_REQUIRED_STATUS = "missing_required_field"

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_helicity_q_scan_N128_20260621.json"
)
DEFAULT_BAND_EPS = 0.05
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_THRESHOLD_VALUES = (0.0, 0.5, 1.0, 2.0, 4.0)

CONTROL_CARD = {
    "O": "Scan raw N128 boundary-band helicity and off-diagonal pressure observable Q.",
    "R": (
        "Reconstruct boundary-band Route 1 observables on |lambda2|<=band_eps, compute "
        "local helicity u·omega alongside Q, and emit sign/co-movement telemetry by delta1 threshold."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical scan only; malformed frames or non-finite arithmetic degrade explicitly.",
    "L": (
        "Load raw frames, reconstruct strain boundary bands and Q, compute local helicity, "
        "bin by delta1 thresholds, and aggregate framewise sign statistics."
    ),
    "P": ROUTE_DECISION,
    "G": "Empirical/non-promoting only; no helicity-Q sign theorem or Clay claim is inferred.",
    "F": "Boundary helicity/Q coupling remains telemetry rather than proof.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--band-eps", type=float, default=DEFAULT_BAND_EPS)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument(
        "--delta1-threshold",
        type=float,
        action="append",
        dest="delta1_thresholds",
        help="Repeatable delta1 threshold. Defaults to a standard set if omitted.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _coerce_thresholds(values: list[float] | None) -> list[float]:
    if not values:
        return [float(x) for x in DEFAULT_THRESHOLD_VALUES]
    kept: list[float] = []
    seen: set[float] = set()
    for raw in values:
        value = float(raw)
        if not math.isfinite(value) or value < 0.0:
            continue
        key = float(f"{value:.12g}")
        if key in seen:
            continue
        seen.add(key)
        kept.append(key)
    kept.sort()
    return kept


def _helicity_field(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    n = int(u.shape[0])
    spacing = float(domain_length) / float(n)
    k = 2.0 * math.pi * np.fft.fftfreq(n, d=spacing)
    kx = k.reshape(n, 1, 1)
    ky = k.reshape(1, n, 1)
    kz = k.reshape(1, 1, n)

    du_dy = _spectral_derivative(u, 1, kx, ky, kz)
    du_dz = _spectral_derivative(u, 2, kx, ky, kz)
    dv_dx = _spectral_derivative(v, 0, kx, ky, kz)
    dv_dz = _spectral_derivative(v, 2, kx, ky, kz)
    dw_dx = _spectral_derivative(w, 0, kx, ky, kz)
    dw_dy = _spectral_derivative(w, 1, kx, ky, kz)

    omega_x = dw_dy - dv_dz
    omega_y = du_dz - dw_dx
    omega_z = dv_dx - du_dy
    return (u * omega_x) + (v * omega_y) + (w * omega_z)


def _threshold_row(
    threshold: float,
    delta1: np.ndarray,
    q: np.ndarray,
    helicity: np.ndarray,
    boundary_count: int,
    eps: float,
) -> dict[str, Any]:
    mask = delta1 >= float(threshold)
    active = int(np.count_nonzero(mask))
    if active == 0:
        return {
            "delta1_threshold": float(threshold),
            "active_count": 0,
            "active_fraction_of_boundary": 0.0,
            "q_negative_fraction": 0.0,
            "helicity_positive_fraction": 0.0,
            "helicity_negative_fraction": 0.0,
            "depleting_pair_fraction": 0.0,
            "anti_depleting_pair_fraction": 0.0,
            "q_helicity_correlation": None,
            "delta1_min": None,
            "q_mean": 0.0,
            "helicity_mean": 0.0,
            "abs_q_mean": 0.0,
            "abs_helicity_mean": 0.0,
        }
    delta1_a = np.asarray(delta1[mask], dtype=np.float64)
    q_a = np.asarray(q[mask], dtype=np.float64)
    h_a = np.asarray(helicity[mask], dtype=np.float64)
    return {
        "delta1_threshold": float(threshold),
        "active_count": active,
        "active_fraction_of_boundary": _fraction(active, boundary_count),
        "q_negative_fraction": _fraction(int(np.count_nonzero(q_a < -eps)), active),
        "helicity_positive_fraction": _fraction(int(np.count_nonzero(h_a > eps)), active),
        "helicity_negative_fraction": _fraction(int(np.count_nonzero(h_a < -eps)), active),
        "depleting_pair_fraction": _fraction(int(np.count_nonzero((q_a < -eps) & (h_a > eps))), active),
        "anti_depleting_pair_fraction": _fraction(int(np.count_nonzero((q_a > eps) & (h_a < -eps))), active),
        "q_helicity_correlation": _pearson(q_a.tolist(), h_a.tolist()),
        "delta1_min": float(np.min(delta1_a)),
        "q_mean": float(np.mean(q_a)),
        "helicity_mean": float(np.mean(h_a)),
        "abs_q_mean": float(np.mean(np.abs(q_a))),
        "abs_helicity_mean": float(np.mean(np.abs(h_a))),
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    band_eps: float,
    zero_eps: float,
    thresholds: list[float],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "band_eps": float(band_eps),
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        p = _frame_pressure(bundle, snapshot)
        obs = _reconstruct_boundary_observables(u, v, w, p, bundle.domain_length)
        helicity = _helicity_field(u, v, w, bundle.domain_length)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_reconstruction_error: {exc}"]
        return ERROR_STATUS, row

    finite = np.isfinite(helicity)
    for value in obs.values():
        finite &= np.isfinite(value)
    finite_count = int(np.count_nonzero(finite))
    row["finite_cell_count"] = finite_count
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite reconstructed cells"]
        return ERROR_STATUS, row

    boundary_mask = finite & (np.abs(obs["lambda2"]) <= float(band_eps))
    boundary_count = int(np.count_nonzero(boundary_mask))
    row["boundary_cell_count"] = boundary_count
    row["boundary_fraction"] = _fraction(boundary_count, finite_count)
    if boundary_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["errors"] = ["no boundary-band cells for |lambda2| <= band_eps"]
        row["threshold_rows"] = [_threshold_row(t, np.array([]), np.array([]), np.array([]), 0, zero_eps) for t in thresholds]
        return MISSING_REQUIRED_STATUS, row

    delta1 = np.abs(obs["lambda1"][boundary_mask])
    q = np.asarray(obs["q"][boundary_mask], dtype=np.float64)
    h_a = np.asarray(helicity[boundary_mask], dtype=np.float64)

    row["delta1_min"] = float(np.min(delta1))
    row["delta1_max"] = float(np.max(delta1))
    row["delta1_mean"] = float(np.mean(delta1))
    row["q_negative_fraction"] = _fraction(int(np.count_nonzero(q < -zero_eps)), boundary_count)
    row["helicity_positive_fraction"] = _fraction(int(np.count_nonzero(h_a > zero_eps)), boundary_count)
    row["helicity_negative_fraction"] = _fraction(int(np.count_nonzero(h_a < -zero_eps)), boundary_count)
    row["depleting_pair_fraction"] = _fraction(int(np.count_nonzero((q < -zero_eps) & (h_a > zero_eps))), boundary_count)
    row["anti_depleting_pair_fraction"] = _fraction(int(np.count_nonzero((q > zero_eps) & (h_a < -zero_eps))), boundary_count)
    row["q_helicity_correlation"] = _pearson(q.tolist(), h_a.tolist())
    row["q_mean"] = float(np.mean(q))
    row["helicity_mean"] = float(np.mean(h_a))
    row["abs_q_mean"] = float(np.mean(np.abs(q)))
    row["abs_helicity_mean"] = float(np.mean(np.abs(h_a)))
    row["threshold_rows"] = [_threshold_row(t, delta1, q, h_a, boundary_count, zero_eps) for t in thresholds]
    row["status"] = OK_STATUS
    return OK_STATUS, row


def main() -> int:
    args = _parse_args()
    thresholds = _coerce_thresholds(args.delta1_thresholds)
    warnings: list[str] = []
    payload: dict[str, Any] = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": _authority(),
        "parameters": {
            "band_eps": float(args.band_eps),
            "zero_eps": float(args.zero_eps),
            "delta1_thresholds": thresholds,
        },
        "raw_archive": str(args.raw_archive),
    }
    try:
        bundle = _load_raw_bundle(args.raw_archive, warnings)
        frames = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    except Exception as exc:  # noqa: BLE001
        payload["status"] = ERROR_STATUS
        payload["errors"] = [str(exc)]
        payload["warnings"] = warnings
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    frame_rows: list[dict[str, Any]] = []
    saw_error = False
    saw_missing = False
    per_threshold_rows: dict[float, list[dict[str, Any]]] = {float(t): [] for t in thresholds}
    q_negative_means: list[float] = []
    depleting_pair_means: list[float] = []
    for slot, snapshot in enumerate(frames):
        status, row = _evaluate_frame(
            slot,
            snapshot,
            bundle,
            float(args.band_eps),
            float(args.zero_eps),
            thresholds,
        )
        frame_rows.append(row)
        for trow in row.get("threshold_rows", []):
            per_threshold_rows.setdefault(float(trow["delta1_threshold"]), []).append(trow)
        if status == OK_STATUS:
            q_negative_means.append(float(row["q_negative_fraction"]))
            depleting_pair_means.append(float(row["depleting_pair_fraction"]))
        elif status == ERROR_STATUS:
            saw_error = True
        else:
            saw_missing = True

    aggregate_rows: list[dict[str, Any]] = []
    for threshold in thresholds:
        rows = per_threshold_rows.get(float(threshold), [])
        active_total = int(sum(int(r.get("active_count", 0)) for r in rows))
        if active_total <= 0:
            aggregate_rows.append(
                {
                    "delta1_threshold": float(threshold),
                    "active_count": 0,
                    "q_negative_fraction": 0.0,
                    "helicity_positive_fraction": 0.0,
                    "helicity_negative_fraction": 0.0,
                    "depleting_pair_fraction": 0.0,
                    "anti_depleting_pair_fraction": 0.0,
                    "q_helicity_correlation_mean": None,
                    "delta1_min": None,
                    "q_mean": 0.0,
                    "helicity_mean": 0.0,
                }
            )
            continue
        def weighted_mean(name: str) -> float:
            return sum(float(r.get(name, 0.0)) * int(r.get("active_count", 0)) for r in rows) / float(active_total)
        corr_values = [float(r["q_helicity_correlation"]) for r in rows if r.get("q_helicity_correlation") is not None]
        mins = [float(r["delta1_min"]) for r in rows if r.get("delta1_min") is not None]
        aggregate_rows.append(
            {
                "delta1_threshold": float(threshold),
                "active_count": active_total,
                "q_negative_fraction": weighted_mean("q_negative_fraction"),
                "helicity_positive_fraction": weighted_mean("helicity_positive_fraction"),
                "helicity_negative_fraction": weighted_mean("helicity_negative_fraction"),
                "depleting_pair_fraction": weighted_mean("depleting_pair_fraction"),
                "anti_depleting_pair_fraction": weighted_mean("anti_depleting_pair_fraction"),
                "q_helicity_correlation_mean": float(np.mean(corr_values)) if corr_values else None,
                "delta1_min": float(min(mins)) if mins else None,
                "q_mean": weighted_mean("q_mean"),
                "helicity_mean": weighted_mean("helicity_mean"),
                "abs_q_mean": weighted_mean("abs_q_mean"),
                "abs_helicity_mean": weighted_mean("abs_helicity_mean"),
            }
        )

    status = OK_STATUS
    if saw_error:
        status = PARTIAL_STATUS if frame_rows else ERROR_STATUS
    elif saw_missing:
        status = PARTIAL_STATUS

    payload["status"] = status
    payload["frame_rows"] = frame_rows
    payload["aggregate"] = {
        "processed_frames": len(frames),
        "ok_frames": sum(1 for row in frame_rows if row.get("status") == OK_STATUS),
        "threshold_rows": aggregate_rows,
        "q_negative_fraction_mean": float(np.mean(q_negative_means)) if q_negative_means else 0.0,
        "depleting_pair_fraction_mean": float(np.mean(depleting_pair_means)) if depleting_pair_means else 0.0,
        "q_negative_vs_depleting_pair_correlation": _pearson(q_negative_means, depleting_pair_means),
    }
    if warnings:
        payload["warnings"] = warnings
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status in {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS} else 1


if __name__ == "__main__":
    raise SystemExit(main())
