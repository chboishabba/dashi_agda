#!/usr/bin/env python3
"""Scan boundary-band pressure-Hessian observables on the raw N128 archive."""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_pressure_eigenframe_gap_scan import (  # type: ignore
    _frame_pressure,
    _frame_velocity,
    _load_raw_bundle,
    _spectral_derivative,
    _spectral_hessian,
)


SCRIPT_NAME = "scripts/ns_boundary_pressure_gate_scan.py"
CONTRACT = "ns_boundary_pressure_gate_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_GATE_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_pressure_gate_scan_N128_20260621.json"
)
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_BAND_EPS = 0.05
DEFAULT_THRESHOLD_VALUES = (0.0, 0.5, 1.0, 2.0, 4.0)

CONTROL_CARD = {
    "O": "Scan raw N128 pressure-boundary observables on the lambda2 boundary band.",
    "R": (
        "Reconstruct strain and pressure Hessian from the raw archive, restrict to "
        "|lambda2| <= band_eps, and emit P11/P22/P33/Q boundary telemetry grouped "
        "by delta1 thresholds."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical scan: malformed frames or arithmetic violations degrade explicitly.",
    "L": (
        "Load raw frames, reconstruct strain eigenframes and pressure Hessian, project "
        "boundary-band observables, aggregate per-frame and threshold telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "Empirical non-promoting scan only; no theorem or Clay claim is inferred.",
    "F": "Missing boundary cells, malformed payloads, or non-finite arithmetic remain explicit errors/partials.",
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


def _authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


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


def _frame_indices(frame_count: int, frame: int | None, frame_limit: int | None) -> list[int]:
    if frame is not None:
        if frame < 0 or frame >= frame_count:
            raise ValueError(f"frame {frame} out of range for frame_count={frame_count}")
        return [int(frame)]
    limit = frame_count if frame_limit is None else min(frame_count, max(0, int(frame_limit)))
    return list(range(limit))


def _pearson(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    x = np.asarray(xs, dtype=np.float64)
    y = np.asarray(ys, dtype=np.float64)
    if not np.all(np.isfinite(x)) or not np.all(np.isfinite(y)):
        return None
    x_std = float(np.std(x))
    y_std = float(np.std(y))
    if x_std <= 0.0 or y_std <= 0.0:
        return None
    return float(np.corrcoef(x, y)[0, 1])


def _boundary_threshold_row(
    threshold: float,
    delta1: np.ndarray,
    p11: np.ndarray,
    p22: np.ndarray,
    p33: np.ndarray,
    q: np.ndarray,
    h_values: np.ndarray,
    omega2_dominant: np.ndarray,
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
            "q_positive_fraction": 0.0,
            "p11_negative_fraction": 0.0,
            "p22_negative_fraction": 0.0,
            "p33_negative_fraction": 0.0,
            "omega2_dominant_fraction": 0.0,
            "delta1_min": None,
            "delta1_mean": 0.0,
            "q_mean": 0.0,
            "q_abs_mean": 0.0,
            "p11_mean": 0.0,
            "p22_mean": 0.0,
            "p33_mean": 0.0,
            "h_mean": 0.0,
            "q_quantiles": {},
            "p11_quantiles": {},
        }

    delta1_a = np.asarray(delta1[mask], dtype=np.float64)
    p11_a = np.asarray(p11[mask], dtype=np.float64)
    p22_a = np.asarray(p22[mask], dtype=np.float64)
    p33_a = np.asarray(p33[mask], dtype=np.float64)
    q_a = np.asarray(q[mask], dtype=np.float64)
    h_a = np.asarray(h_values[mask], dtype=np.float64)
    omega2_a = np.asarray(omega2_dominant[mask], dtype=np.bool_)

    q_qs = np.quantile(q_a, [0.1, 0.5, 0.9]).tolist()
    p11_qs = np.quantile(p11_a, [0.1, 0.5, 0.9]).tolist()
    return {
        "delta1_threshold": float(threshold),
        "active_count": active,
        "active_fraction_of_boundary": _fraction(active, boundary_count),
        "q_negative_fraction": _fraction(int(np.count_nonzero(q_a < -eps)), active),
        "q_positive_fraction": _fraction(int(np.count_nonzero(q_a > eps)), active),
        "p11_negative_fraction": _fraction(int(np.count_nonzero(p11_a < -eps)), active),
        "p22_negative_fraction": _fraction(int(np.count_nonzero(p22_a < -eps)), active),
        "p33_negative_fraction": _fraction(int(np.count_nonzero(p33_a < -eps)), active),
        "omega2_dominant_fraction": _fraction(int(np.count_nonzero(omega2_a)), active),
        "delta1_min": float(np.min(delta1_a)),
        "delta1_mean": float(np.mean(delta1_a)),
        "q_mean": float(np.mean(q_a)),
        "q_abs_mean": float(np.mean(np.abs(q_a))),
        "p11_mean": float(np.mean(p11_a)),
        "p22_mean": float(np.mean(p22_a)),
        "p33_mean": float(np.mean(p33_a)),
        "h_mean": float(np.mean(h_a)),
        "q_quantiles": {"q10": float(q_qs[0]), "q50": float(q_qs[1]), "q90": float(q_qs[2])},
        "p11_quantiles": {"q10": float(p11_qs[0]), "q50": float(p11_qs[1]), "q90": float(p11_qs[2])},
    }


def _reconstruct_boundary_observables(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    p: np.ndarray,
    domain_length: float,
) -> dict[str, np.ndarray]:
    if not (u.shape == v.shape == w.shape == p.shape):
        raise ValueError("u, v, w, p shapes must agree")
    if u.ndim != 3:
        raise ValueError(f"snapshot fields must be 3D, got {u.shape!r}")

    n = int(u.shape[0])
    spacing = float(domain_length) / float(n)
    k = 2.0 * math.pi * np.fft.fftfreq(n, d=spacing)
    kx = k.reshape(n, 1, 1)
    ky = k.reshape(1, n, 1)
    kz = k.reshape(1, 1, n)

    du_dx = _spectral_derivative(u, 0, kx, ky, kz)
    du_dy = _spectral_derivative(u, 1, kx, ky, kz)
    du_dz = _spectral_derivative(u, 2, kx, ky, kz)
    dv_dx = _spectral_derivative(v, 0, kx, ky, kz)
    dv_dy = _spectral_derivative(v, 1, kx, ky, kz)
    dv_dz = _spectral_derivative(v, 2, kx, ky, kz)
    dw_dx = _spectral_derivative(w, 0, kx, ky, kz)
    dw_dy = _spectral_derivative(w, 1, kx, ky, kz)
    dw_dz = _spectral_derivative(w, 2, kx, ky, kz)

    strain = np.empty(u.shape + (3, 3), dtype=np.float64)
    strain[..., 0, 0] = du_dx
    strain[..., 1, 1] = dv_dy
    strain[..., 2, 2] = dw_dz
    strain[..., 0, 1] = 0.5 * (du_dy + dv_dx)
    strain[..., 1, 0] = strain[..., 0, 1]
    strain[..., 0, 2] = 0.5 * (du_dz + dw_dx)
    strain[..., 2, 0] = strain[..., 0, 2]
    strain[..., 1, 2] = 0.5 * (dv_dz + dw_dy)
    strain[..., 2, 1] = strain[..., 1, 2]

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    lambda1 = np.asarray(eigenvalues[..., 0], dtype=np.float64)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    lambda3 = np.asarray(eigenvalues[..., 2], dtype=np.float64)

    hessian = _spectral_hessian(p, domain_length)
    h_tensor = np.moveaxis(hessian, (0, 1), (-2, -1))
    projected = np.einsum("...ia,...ij,...jb->...ab", eigenvectors, h_tensor, eigenvectors)

    omega_x = dw_dy - dv_dz
    omega_y = du_dz - dw_dx
    omega_z = dv_dx - du_dy
    omega_norm_sq = omega_x * omega_x + omega_y * omega_y + omega_z * omega_z

    e1 = np.asarray(eigenvectors[..., :, 0], dtype=np.float64)
    e2 = np.asarray(eigenvectors[..., :, 1], dtype=np.float64)
    e3 = np.asarray(eigenvectors[..., :, 2], dtype=np.float64)

    omega1 = omega_x * e1[..., 0] + omega_y * e1[..., 1] + omega_z * e1[..., 2]
    omega2 = omega_x * e2[..., 0] + omega_y * e2[..., 1] + omega_z * e2[..., 2]
    omega3 = omega_x * e3[..., 0] + omega_y * e3[..., 1] + omega_z * e3[..., 2]

    strain_frob_sq = np.sum(strain * strain, axis=(-2, -1))
    h_values = strain_frob_sq - 0.5 * omega_norm_sq

    return {
        "lambda1": lambda1,
        "lambda2": lambda2,
        "lambda3": lambda3,
        "p11": np.asarray(projected[..., 0, 0], dtype=np.float64),
        "p22": np.asarray(projected[..., 1, 1], dtype=np.float64),
        "p33": np.asarray(projected[..., 2, 2], dtype=np.float64),
        "q": np.asarray(projected[..., 1, 0], dtype=np.float64),
        "h": np.asarray(h_values, dtype=np.float64),
        "omega1_sq": np.asarray(omega1 * omega1, dtype=np.float64),
        "omega2_sq": np.asarray(omega2 * omega2, dtype=np.float64),
        "omega3_sq": np.asarray(omega3 * omega3, dtype=np.float64),
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    band_eps: float,
    zero_eps: float,
    thresholds: list[float],
) -> tuple[str, dict[str, Any], list[str]]:
    warnings: list[str] = []
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
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_reconstruction_error: {exc}"]
        return ERROR_STATUS, row, warnings

    finite = np.ones_like(obs["lambda1"], dtype=bool)
    for value in obs.values():
        finite &= np.isfinite(value)

    finite_count = int(np.count_nonzero(finite))
    row["finite_cell_count"] = finite_count
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite reconstructed cells"]
        return ERROR_STATUS, row, warnings

    boundary_mask = finite & (np.abs(obs["lambda2"]) <= float(band_eps))
    boundary_count = int(np.count_nonzero(boundary_mask))
    row["boundary_cell_count"] = boundary_count
    row["boundary_fraction"] = _fraction(boundary_count, finite_count)
    if boundary_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["errors"] = ["no boundary-band cells for |lambda2| <= band_eps"]
        row["threshold_rows"] = [_boundary_threshold_row(t, np.array([]), np.array([]), np.array([]), np.array([]), np.array([]), np.array([]), np.array([], dtype=bool), 0, zero_eps) for t in thresholds]
        return MISSING_REQUIRED_STATUS, row, warnings

    delta1 = np.abs(obs["lambda1"][boundary_mask])
    p11 = obs["p11"][boundary_mask]
    p22 = obs["p22"][boundary_mask]
    p33 = obs["p33"][boundary_mask]
    q = obs["q"][boundary_mask]
    h_values = obs["h"][boundary_mask]
    omega2_dom = obs["omega2_sq"][boundary_mask] >= np.maximum(obs["omega1_sq"][boundary_mask], obs["omega3_sq"][boundary_mask])

    row["delta1_min"] = float(np.min(delta1))
    row["delta1_max"] = float(np.max(delta1))
    row["delta1_mean"] = float(np.mean(delta1))
    row["q_negative_fraction"] = _fraction(int(np.count_nonzero(q < -zero_eps)), boundary_count)
    row["q_positive_fraction"] = _fraction(int(np.count_nonzero(q > zero_eps)), boundary_count)
    row["p11_negative_fraction"] = _fraction(int(np.count_nonzero(p11 < -zero_eps)), boundary_count)
    row["p22_negative_fraction"] = _fraction(int(np.count_nonzero(p22 < -zero_eps)), boundary_count)
    row["p33_negative_fraction"] = _fraction(int(np.count_nonzero(p33 < -zero_eps)), boundary_count)
    row["omega2_dominant_fraction"] = _fraction(int(np.count_nonzero(omega2_dom)), boundary_count)
    row["q_mean"] = float(np.mean(q))
    row["q_abs_mean"] = float(np.mean(np.abs(q)))
    row["p11_mean"] = float(np.mean(p11))
    row["p22_mean"] = float(np.mean(p22))
    row["p33_mean"] = float(np.mean(p33))
    row["h_mean"] = float(np.mean(h_values))
    row["threshold_rows"] = [
        _boundary_threshold_row(t, delta1, p11, p22, p33, q, h_values, omega2_dom, boundary_count, zero_eps)
        for t in thresholds
    ]
    row["status"] = OK_STATUS
    return OK_STATUS, row, warnings


def main() -> int:
    args = _parse_args()
    thresholds = _coerce_thresholds(args.delta1_thresholds)
    warnings: list[str] = []
    errors: list[str] = []

    payload: dict[str, Any] = {
        "O": CONTROL_CARD["O"],
        "R": CONTROL_CARD["R"],
        "C": CONTROL_CARD["C"],
        "S": CONTROL_CARD["S"],
        "L": CONTROL_CARD["L"],
        "P": CONTROL_CARD["P"],
        "G": CONTROL_CARD["G"],
        "F": CONTROL_CARD["F"],
        "control_card": CONTROL_CARD,
        "authority": _authority(),
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
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
    status_counts = {key: 0 for key in sorted(ALLOWED_STATUSES)}
    all_threshold_rows: dict[float, list[dict[str, Any]]] = {float(t): [] for t in thresholds}
    q_negative_means: list[float] = []
    p11_negative_means: list[float] = []
    omega2_means: list[float] = []

    for slot, snapshot in enumerate(frames):
        status, row, frame_warnings = _evaluate_frame(
            slot,
            snapshot,
            bundle,
            float(args.band_eps),
            float(args.zero_eps),
            thresholds,
        )
        frame_rows.append(row)
        warnings.extend(frame_warnings)
        status_counts[status] = status_counts.get(status, 0) + 1
        for threshold_row in row.get("threshold_rows", []):
            key = float(threshold_row["delta1_threshold"])
            all_threshold_rows.setdefault(key, []).append(threshold_row)
        if status == OK_STATUS:
            q_negative_means.append(float(row["q_negative_fraction"]))
            p11_negative_means.append(float(row["p11_negative_fraction"]))
            omega2_means.append(float(row["omega2_dominant_fraction"]))

    aggregate_rows: list[dict[str, Any]] = []
    for threshold in thresholds:
        rows = all_threshold_rows.get(float(threshold), [])
        active_count = int(sum(int(r.get("active_count", 0)) for r in rows))
        boundary_count = int(sum(int(r.get("active_count", 0) / max(float(r.get("active_fraction_of_boundary", 0.0)), 1.0e-12)) if float(r.get("active_fraction_of_boundary", 0.0)) > 0.0 else 0 for r in rows))
        q_means = [float(r["q_mean"]) for r in rows if r.get("active_count", 0) > 0]
        p11_means = [float(r["p11_mean"]) for r in rows if r.get("active_count", 0) > 0]
        p22_means = [float(r["p22_mean"]) for r in rows if r.get("active_count", 0) > 0]
        p33_means = [float(r["p33_mean"]) for r in rows if r.get("active_count", 0) > 0]
        h_means = [float(r["h_mean"]) for r in rows if r.get("active_count", 0) > 0]
        delta1_mins = [float(r["delta1_min"]) for r in rows if r.get("delta1_min") is not None]
        q_neg_num = sum(float(r["q_negative_fraction"]) * int(r["active_count"]) for r in rows)
        p11_neg_num = sum(float(r["p11_negative_fraction"]) * int(r["active_count"]) for r in rows)
        omega2_num = sum(float(r["omega2_dominant_fraction"]) * int(r["active_count"]) for r in rows)
        if active_count == 0:
            aggregate_rows.append(
                {
                    "delta1_threshold": float(threshold),
                    "active_count": 0,
                    "active_fraction_of_boundary": 0.0,
                    "q_negative_fraction": 0.0,
                    "p11_negative_fraction": 0.0,
                    "omega2_dominant_fraction": 0.0,
                    "delta1_min": None,
                    "q_mean": 0.0,
                    "p11_mean": 0.0,
                    "p22_mean": 0.0,
                    "p33_mean": 0.0,
                    "h_mean": 0.0,
                }
            )
            continue
        aggregate_rows.append(
            {
                "delta1_threshold": float(threshold),
                "active_count": active_count,
                "active_fraction_of_boundary": _fraction(active_count, boundary_count),
                "q_negative_fraction": q_neg_num / float(active_count),
                "p11_negative_fraction": p11_neg_num / float(active_count),
                "omega2_dominant_fraction": omega2_num / float(active_count),
                "delta1_min": float(min(delta1_mins)) if delta1_mins else None,
                "q_mean": float(np.mean(q_means)) if q_means else 0.0,
                "p11_mean": float(np.mean(p11_means)) if p11_means else 0.0,
                "p22_mean": float(np.mean(p22_means)) if p22_means else 0.0,
                "p33_mean": float(np.mean(p33_means)) if p33_means else 0.0,
                "h_mean": float(np.mean(h_means)) if h_means else 0.0,
            }
        )

    status = OK_STATUS
    if status_counts[ERROR_STATUS] > 0:
        status = PARTIAL_STATUS if status_counts[OK_STATUS] > 0 else ERROR_STATUS
    elif status_counts[MISSING_REQUIRED_STATUS] > 0:
        status = PARTIAL_STATUS if status_counts[OK_STATUS] > 0 else MISSING_REQUIRED_STATUS

    payload["status"] = status
    payload["status_counts"] = status_counts
    payload["frame_rows"] = frame_rows
    payload["aggregate"] = {
        "processed_frames": len(frames),
        "ok_frames": status_counts[OK_STATUS],
        "boundary_threshold_rows": aggregate_rows,
        "q_negative_fraction_mean": float(np.mean(q_negative_means)) if q_negative_means else 0.0,
        "p11_negative_fraction_mean": float(np.mean(p11_negative_means)) if p11_negative_means else 0.0,
        "omega2_dominant_fraction_mean": float(np.mean(omega2_means)) if omega2_means else 0.0,
        "q_vs_p11_negative_fraction_correlation": _pearson(q_negative_means, p11_negative_means),
        "q_vs_omega2_dominant_fraction_correlation": _pearson(q_negative_means, omega2_means),
    }
    if warnings:
        payload["warnings"] = warnings
    if errors:
        payload["errors"] = errors

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status in {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS} else 1


if __name__ == "__main__":
    raise SystemExit(main())
