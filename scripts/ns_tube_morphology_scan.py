#!/usr/bin/env python3
"""Scan simple tube/sheet/blob morphology proxies on the raw N128 archive."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_pressure_eigenframe_gap_scan import (  # type: ignore
    _authority,
    _frame_velocity,
    _load_raw_bundle,
    _spectral_derivative,
    _spectral_hessian,
)


SCRIPT_NAME = "scripts/ns_tube_morphology_scan.py"
CONTRACT = "ns_tube_morphology_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TUBE_MORPHOLOGY_SCAN"
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
    "ns_tube_morphology_scan_N128_20260621.json"
)
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_CARRIER_QUANTILES = (0.95, 0.99)
DEFAULT_AXIS_RATIO = 0.20
DEFAULT_NEG_RATIO = 0.35

CONTROL_CARD = {
    "O": "Scan raw N128 high-enstrophy morphology on reconstructed local carriers.",
    "R": (
        "Classify high-enstrophy voxels by simple Hessian-based local morphology "
        "proxies (tube-like, sheet-like, blob-like, ambiguous) and report framewise "
        "plus aggregate telemetry."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical scan only; malformed fields or non-finite arithmetic become explicit degraded states.",
    "L": (
        "Load raw velocity frames, reconstruct vorticity and enstrophy Hessians, "
        "threshold high-enstrophy carriers, classify local morphology, and aggregate "
        "quantile rows."
    ),
    "P": ROUTE_DECISION,
    "G": "Empirical/non-promoting only; no tube-structure theorem or Clay claim is inferred.",
    "F": "Morphology is proxied from framewise local Hessian geometry and remains telemetry rather than proof.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument(
        "--carrier-quantile",
        type=float,
        action="append",
        dest="carrier_quantiles",
        help="Repeatable carrier quantile in [0,1]. Defaults to 0.95 and 0.99.",
    )
    parser.add_argument("--axis-ratio", type=float, default=DEFAULT_AXIS_RATIO)
    parser.add_argument("--neg-ratio", type=float, default=DEFAULT_NEG_RATIO)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _frame_indices(frame_count: int, frame: int | None, frame_limit: int | None) -> list[int]:
    if frame is not None:
        if frame < 0 or frame >= frame_count:
            raise ValueError(f"frame {frame} out of range for frame_count={frame_count}")
        return [int(frame)]
    if frame_limit is None:
        return list(range(frame_count))
    return list(range(min(frame_count, max(0, int(frame_limit)))))


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _coerce_quantiles(values: list[float] | None) -> list[float]:
    if not values:
        return [float(v) for v in DEFAULT_CARRIER_QUANTILES]
    kept: list[float] = []
    seen: set[float] = set()
    for raw in values:
        value = float(raw)
        if not math.isfinite(value) or value <= 0.0 or value >= 1.0:
            continue
        key = float(f"{value:.12g}")
        if key in seen:
            continue
        seen.add(key)
        kept.append(key)
    kept.sort()
    return kept


def _reconstruct_morphology_fields(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> dict[str, np.ndarray]:
    if not (u.shape == v.shape == w.shape):
        raise ValueError("velocity component shapes must match")
    if u.ndim != 3:
        raise ValueError(f"velocity fields must be 3D, got {u.shape!r}")

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
    omega_norm_sq = omega_x * omega_x + omega_y * omega_y + omega_z * omega_z

    hessian = _spectral_hessian(np.asarray(omega_norm_sq, dtype=np.float64), domain_length)
    h_tensor = np.moveaxis(hessian, (0, 1), (-2, -1))
    eigenvalues, eigenvectors = np.linalg.eigh(h_tensor)

    omega = np.stack((omega_x, omega_y, omega_z), axis=-1)
    omega_norm = np.sqrt(np.maximum(omega_norm_sq, 0.0))
    omega_hat = np.zeros_like(omega, dtype=np.float64)
    safe = omega_norm > 0.0
    omega_hat[safe] = omega[safe] / omega_norm[safe, None]

    axis_vector = np.asarray(eigenvectors[..., :, 2], dtype=np.float64)
    axis_alignment = np.abs(np.sum(omega_hat * axis_vector, axis=-1))

    return {
        "omega_norm_sq": np.asarray(omega_norm_sq, dtype=np.float64),
        "hessian_eigenvalues": np.asarray(eigenvalues, dtype=np.float64),
        "axis_alignment": np.asarray(axis_alignment, dtype=np.float64),
    }


def _classify_rows(
    carrier_values: np.ndarray,
    hessian_eigenvalues: np.ndarray,
    axis_alignment: np.ndarray,
    zero_eps: float,
    axis_ratio: float,
    neg_ratio: float,
) -> dict[str, Any]:
    if carrier_values.size == 0:
        return {
            "carrier_count": 0,
            "tube_like_fraction": 0.0,
            "sheet_like_fraction": 0.0,
            "blob_like_fraction": 0.0,
            "ambiguous_fraction": 0.0,
            "tube_axis_alignment_mean": 0.0,
            "carrier_mean": 0.0,
            "carrier_min": 0.0,
            "carrier_max": 0.0,
        }

    eig = np.asarray(hessian_eigenvalues, dtype=np.float64)
    lam0 = eig[:, 0]
    lam1 = eig[:, 1]
    lam2 = eig[:, 2]

    strong = np.maximum(np.maximum(np.abs(lam0), np.abs(lam1)), np.abs(lam2))
    neg0 = lam0 < -zero_eps
    neg1 = lam1 < -zero_eps
    neg2 = lam2 < -zero_eps
    near0 = np.abs(lam2) <= axis_ratio * np.maximum(np.maximum(np.abs(lam0), np.abs(lam1)), zero_eps)
    near1 = np.abs(lam1) <= axis_ratio * np.maximum(np.abs(lam0), zero_eps)
    near2 = np.abs(lam2) <= axis_ratio * np.maximum(np.abs(lam0), zero_eps)

    tube = neg0 & neg1 & (~neg2) & near0
    sheet = neg0 & (~neg1) & near1 & near2
    blob = neg0 & neg1 & neg2 & (np.abs(lam2) > neg_ratio * np.maximum(np.abs(lam0), zero_eps))
    ambiguous = ~(tube | sheet | blob)

    tube_align = np.asarray(axis_alignment[tube], dtype=np.float64)
    return {
        "carrier_count": int(carrier_values.size),
        "tube_like_fraction": _fraction(int(np.count_nonzero(tube)), int(carrier_values.size)),
        "sheet_like_fraction": _fraction(int(np.count_nonzero(sheet)), int(carrier_values.size)),
        "blob_like_fraction": _fraction(int(np.count_nonzero(blob)), int(carrier_values.size)),
        "ambiguous_fraction": _fraction(int(np.count_nonzero(ambiguous)), int(carrier_values.size)),
        "tube_axis_alignment_mean": float(np.mean(tube_align)) if tube_align.size else 0.0,
        "carrier_mean": float(np.mean(carrier_values)),
        "carrier_min": float(np.min(carrier_values)),
        "carrier_max": float(np.max(carrier_values)),
        "principal_curvature_means": {
            "lambda_h1_mean": float(np.mean(lam0)),
            "lambda_h2_mean": float(np.mean(lam1)),
            "lambda_h3_mean": float(np.mean(lam2)),
            "lambda_h_abs_max_mean": float(np.mean(strong)),
        },
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    quantiles: list[float],
    axis_ratio: float,
    neg_ratio: float,
    zero_eps: float,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        fields = _reconstruct_morphology_fields(u, v, w, bundle.domain_length)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_reconstruction_error: {exc}"]
        return ERROR_STATUS, row

    finite = (
        np.isfinite(fields["omega_norm_sq"])
        & np.isfinite(fields["axis_alignment"])
        & np.all(np.isfinite(fields["hessian_eigenvalues"]), axis=-1)
    )
    finite_count = int(np.count_nonzero(finite))
    row["finite_cell_count"] = finite_count
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite cells"]
        return ERROR_STATUS, row

    omega_norm_sq = fields["omega_norm_sq"][finite]
    hessian_eigs = fields["hessian_eigenvalues"][finite]
    axis_alignment = fields["axis_alignment"][finite]

    row["omega_norm_sq_mean"] = float(np.mean(omega_norm_sq))
    row["omega_norm_sq_max"] = float(np.max(omega_norm_sq))

    quantile_rows: list[dict[str, Any]] = []
    for quantile in quantiles:
        threshold = float(np.quantile(omega_norm_sq, quantile))
        carrier_mask = omega_norm_sq >= threshold
        carrier_values = np.asarray(omega_norm_sq[carrier_mask], dtype=np.float64)
        carrier_eigs = np.asarray(hessian_eigs[carrier_mask], dtype=np.float64)
        carrier_alignment = np.asarray(axis_alignment[carrier_mask], dtype=np.float64)
        morph = _classify_rows(
            carrier_values,
            carrier_eigs,
            carrier_alignment,
            float(zero_eps),
            float(axis_ratio),
            float(neg_ratio),
        )
        quantile_rows.append(
            {
                "carrier_quantile": float(quantile),
                "carrier_threshold": threshold,
                "carrier_fraction": _fraction(morph["carrier_count"], finite_count),
                **morph,
            }
        )

    row["quantile_rows"] = quantile_rows
    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate(frame_rows: list[dict[str, Any]], quantiles: list[float]) -> dict[str, Any]:
    ok_rows = [row for row in frame_rows if row.get("status") == OK_STATUS]
    aggregate: dict[str, Any] = {
        "processed_frames": len(frame_rows),
        "ok_frames": len(ok_rows),
        "status_counts": {},
        "quantile_rows": [],
    }
    for row in frame_rows:
        status = str(row.get("status", ERROR_STATUS))
        aggregate["status_counts"][status] = int(aggregate["status_counts"].get(status, 0)) + 1
    if not ok_rows:
        return aggregate

    for quantile in quantiles:
        rows = []
        for row in ok_rows:
            match = next(
                (entry for entry in row.get("quantile_rows", []) if math.isclose(float(entry.get("carrier_quantile", -1.0)), float(quantile))),
                None,
            )
            if match is not None:
                rows.append(match)
        carrier_total = int(sum(int(r.get("carrier_count", 0)) for r in rows))
        if carrier_total <= 0:
            aggregate["quantile_rows"].append(
                {
                    "carrier_quantile": float(quantile),
                    "carrier_count": 0,
                    "tube_like_fraction": 0.0,
                    "sheet_like_fraction": 0.0,
                    "blob_like_fraction": 0.0,
                    "ambiguous_fraction": 0.0,
                    "tube_axis_alignment_mean": 0.0,
                }
            )
            continue
        tube_num = sum(float(r["tube_like_fraction"]) * int(r["carrier_count"]) for r in rows)
        sheet_num = sum(float(r["sheet_like_fraction"]) * int(r["carrier_count"]) for r in rows)
        blob_num = sum(float(r["blob_like_fraction"]) * int(r["carrier_count"]) for r in rows)
        ambiguous_num = sum(float(r["ambiguous_fraction"]) * int(r["carrier_count"]) for r in rows)
        tube_align_num = sum(float(r["tube_axis_alignment_mean"]) * int(r["carrier_count"]) for r in rows)
        aggregate["quantile_rows"].append(
            {
                "carrier_quantile": float(quantile),
                "carrier_count": carrier_total,
                "carrier_fraction_mean": float(np.mean([float(r["carrier_fraction"]) for r in rows])) if rows else 0.0,
                "tube_like_fraction": tube_num / float(carrier_total),
                "sheet_like_fraction": sheet_num / float(carrier_total),
                "blob_like_fraction": blob_num / float(carrier_total),
                "ambiguous_fraction": ambiguous_num / float(carrier_total),
                "tube_axis_alignment_mean": tube_align_num / float(carrier_total),
                "carrier_threshold_mean": float(np.mean([float(r["carrier_threshold"]) for r in rows])) if rows else 0.0,
            }
        )
    return aggregate


def main() -> int:
    args = _parse_args()
    quantiles = _coerce_quantiles(args.carrier_quantiles)
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
            "carrier_quantiles": quantiles,
            "axis_ratio": float(args.axis_ratio),
            "neg_ratio": float(args.neg_ratio),
            "zero_eps": float(args.zero_eps),
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
    for slot, snapshot in enumerate(frames):
        status, row = _evaluate_frame(
            slot,
            snapshot,
            bundle,
            quantiles,
            float(args.axis_ratio),
            float(args.neg_ratio),
            float(args.zero_eps),
        )
        frame_rows.append(row)
        if status == ERROR_STATUS:
            saw_error = True
        if status == MISSING_REQUIRED_STATUS:
            saw_missing = True

    payload["frame_rows"] = frame_rows
    payload["aggregate"] = _aggregate(frame_rows, quantiles)
    payload["status"] = PARTIAL_STATUS if saw_error or saw_missing else OK_STATUS
    if warnings:
        payload["warnings"] = warnings

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if payload["status"] in {OK_STATUS, PARTIAL_STATUS} else 1


if __name__ == "__main__":
    raise SystemExit(main())
