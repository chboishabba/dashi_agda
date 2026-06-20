#!/usr/bin/env python3
"""Scan corrected determinant-side Omega_K sign equivalence on the raw N128 archive."""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_det_omega_k_measure_scan.py"
CONTRACT = "ns_det_omega_k_measure_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_DET_OMEGA_K_MEASURE_SCAN"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_det_omega_k_measure_scan_N128_20260620.json"
)

DEFAULT_ZERO_EPS = 1.0e-12

CONTROL_CARD = {
    "O": "Measure the determinant-side Omega_K equivalence on the raw N128 velocity archive.",
    "R": (
        "Per-frame and aggregate counts/fractions of lambda2-sign and det(S)-sign bins, "
        "and mismatch-bin counts for the corrected rule."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical telemetry: missing/invalid fields only degrade status, never infer authority.",
    "L": "Reconstruct strain from raw velocity per frame, compute lambda2 and det(S), and emit frame/global summaries.",
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion authority is inferred by this script.",
    "F": "Raw-only reconstruction failures and framewise partial coverage are allowed only as explicit telemetry status, not proofs.",
}


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be nonnegative")
    return parsed


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


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


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in payload:
        try:
            meta = json.loads(str(np.asarray(payload["meta_json"]).item()))
        except Exception:
            meta = None
        else:
            if isinstance(meta, dict):
                for key in ("grid_spacing", "dx", "domain_length", "length", "L", "N", "N1", "N2", "N3"):
                    if key in meta and key not in payload:
                        try:
                            payload[key] = np.asarray(meta[key])
                        except Exception:
                            pass
    return payload


def _read_scalar_metadata(data: dict[str, np.ndarray], names: tuple[str, ...]) -> tuple[float | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape == ():
            scalar = value.item()
        elif value.ndim == 0:
            scalar = value.reshape(()).item()
        elif value.ndim == 1 and value.size == 1:
            scalar = value.reshape(()).item()
        else:
            continue
        if isinstance(scalar, (bytes, bytearray, np.bytes_)):
            scalar = bytes(scalar).decode("utf-8")
        if isinstance(scalar, (np.generic,)):
            scalar = scalar.item()
        try:
            return float(scalar), name
        except Exception:
            continue
    return None, None


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _coerce_float(value: Any, *, finite: bool = True, name: str | None = None) -> float:
    parsed = float(value)
    if finite and not math.isfinite(parsed):
        raise ValueError(f"{name or 'value'} must be finite")
    return parsed


def _sign_counts(values: np.ndarray, eps: float) -> tuple[int, int, int]:
    pos = int(np.count_nonzero(values > eps))
    neg = int(np.count_nonzero(values < -eps))
    zero = int(values.size - pos - neg)
    return pos, neg, zero


def _minmax_with_location(values: np.ndarray, mask: np.ndarray) -> tuple[float, float, list[int], list[int]]:
    valid = np.where(mask, values, np.nan)
    finite_count = int(np.count_nonzero(np.isfinite(valid)))
    if finite_count <= 0:
        raise ValueError("no finite values in masked array")
    arg_min = int(np.argmin(np.where(mask, values, np.inf)))
    arg_max = int(np.argmax(np.where(mask, values, -np.inf)))
    return (
        float(np.nanmin(valid)),
        float(np.nanmax(valid)),
        list(map(int, np.unravel_index(arg_min, values.shape))),
        list(map(int, np.unravel_index(arg_max, values.shape))),
    )


def _frame_sort_key(path: Path) -> tuple[int, str]:
    stem = path.stem.lower()
    match = re.search(r"(?:^|[_-])(frame|snapshot)[_-]?(\d+)(?:$|[_-])", stem)
    if match is not None:
        return int(match.group(2)), path.name
    match = re.search(r"(?:^|[_-])(\d+)(?:$|[_-])", stem)
    if match is not None:
        return int(match.group(1)), path.name
    return 10**12, path.name


def _select_velocity_components(data: dict[str, np.ndarray], warnings: list[str]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if "velocity_snapshots" in data:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        if velocity.ndim == 5 and velocity.shape[1] == 3 and velocity.shape[-1] != 3:
            warnings.append("velocity_snapshots axis-1 channel layout detected")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots trailing channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        if velocity.ndim == 4 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots last-axis channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"unsupported velocity_snapshots shape {velocity.shape!r}")

    if "u" in data and "v" in data and "w" in data:
        return (
            np.asarray(data["u"], dtype=np.float64),
            np.asarray(data["v"], dtype=np.float64),
            np.asarray(data["w"], dtype=np.float64),
        )

    if "velocity" in data:
        velocity = np.asarray(data["velocity"], dtype=np.float64)
        if velocity.ndim == 4 and velocity.shape[1] == 3:
            warnings.append("velocity axis-1 channel layout detected")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity trailing channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"unsupported fallback velocity shape {velocity.shape!r}")

    raise ValueError("no raw velocity components found")


def _infer_domain_length(data: dict[str, np.ndarray], n: int, warnings: list[str]) -> float:
    domain_length, domain_key = _read_scalar_metadata(data, ("domain_length", "length", "L", "domain"))
    if domain_length is not None:
        domain_length_f = _coerce_float(domain_length, name=domain_key or "domain_length")
        if domain_length_f <= 0.0:
            raise ValueError("domain_length must be positive")
    else:
        domain_length_f = None

    spacing, spacing_key = _read_scalar_metadata(data, ("grid_spacing", "dx", "dh"))
    if spacing is not None:
        spacing_f = _coerce_float(spacing, name=spacing_key or "grid_spacing")
        if spacing_f <= 0.0:
            raise ValueError("grid_spacing must be positive")
        if domain_length_f is None:
            domain_length_f = float(spacing_f * n)
        elif not math.isclose(domain_length_f, spacing_f * n, rel_tol=1e-8, abs_tol=1e-8):
            warnings.append(
                f"domain_length/grid_spacing mismatch: {domain_length_f} vs {spacing_f * n} (using domain_length)"
            )

    if domain_length_f is not None:
        return domain_length_f

    fallback = 2.0 * math.pi
    warnings.append(f"domain_length unavailable; using fallback {fallback}")
    return fallback


@dataclass(frozen=True)
class RawBundle:
    path: Path
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    has_frame_axis: bool
    frame_count: int
    domain_length: float


def _load_raw_bundle(path: Path, warnings: list[str]) -> RawBundle:
    data = _load_npz(path)
    u, v, w = _select_velocity_components(data, warnings)

    if u.ndim == 4 and v.ndim == 4 and w.ndim == 4:
        if int(u.shape[0]) != 1 and u.shape[1] == u.shape[2] == u.shape[3]:
            has_frame_axis = True
            frame_count = int(u.shape[0])
        elif int(u.shape[0]) == 1 and u.shape[1] == u.shape[2] == u.shape[3]:
            has_frame_axis = False
            frame_count = 1
            u = u[0]
            v = v[0]
            w = w[0]
        else:
            raise ValueError(f"unsupported 4D velocity shape {u.shape!r}")
    elif u.ndim == 3 and v.ndim == 3 and w.ndim == 3:
        has_frame_axis = False
        frame_count = 1
    elif u.ndim == 5 and v.ndim == 5 and w.ndim == 5:
        if int(u.shape[-1]) != 3:
            raise ValueError(f"unsupported 5D velocity shape {u.shape!r}")
        warnings.append("converted legacy (T,N,N,N,3) velocity layout to components")
        u = u[..., 0]
        v = v[..., 1]
        w = w[..., 2]
        has_frame_axis = True
        frame_count = int(u.shape[0])
        if u.ndim != 4:
            raise ValueError(f"unexpected post-conversion velocity rank {u.ndim}")
    else:
        raise ValueError(f"unsupported velocity shape ranks {u.shape!r}")

    if has_frame_axis:
        n = int(u.shape[1])
        if u.shape[1] != u.shape[2] or u.shape[2] != u.shape[3]:
            raise ValueError(f"velocity snapshot shape not cubic: {u.shape!r}")
    else:
        n = int(u.shape[0])
        if u.shape[0] != u.shape[1] or u.shape[1] != u.shape[2]:
            raise ValueError(f"velocity component shape not cubic: {u.shape!r}")
    if n <= 1:
        raise ValueError(f"invalid grid size n={n}")
    if u.shape[0] not in (n,) and not has_frame_axis:
        raise ValueError(f"unexpected non-cubic velocity shape {u.shape!r}")

    if not np.all(np.isfinite(u)) or not np.all(np.isfinite(v)) or not np.all(np.isfinite(w)):
        warnings.append(f"raw velocity contains non-finite values in {path.name}")
        raise ValueError(f"raw velocity contains non-finite values in {path}")

    domain_length = _infer_domain_length(data, n, warnings)
    return RawBundle(
        path=path,
        u=u,
        v=v,
        w=w,
        has_frame_axis=has_frame_axis,
        frame_count=frame_count,
        domain_length=domain_length,
    )


def _raw_velocity_frame(bundle: RawBundle, snapshot: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if not bundle.has_frame_axis:
        if snapshot != 0:
            raise ValueError(f"raw archive has no frame axis; requested snapshot {snapshot}")
        u = np.asarray(bundle.u, dtype=np.float64)
        v = np.asarray(bundle.v, dtype=np.float64)
        w = np.asarray(bundle.w, dtype=np.float64)
        if u.ndim != 3:
            raise ValueError(f"velocity without frame axis must be 3D, got {u.shape!r}")
        return u, v, w

    if snapshot < 0 or snapshot >= int(bundle.frame_count):
        raise ValueError(f"requested snapshot {snapshot} is out of range for {bundle.frame_count} frames")
    u = np.asarray(bundle.u, dtype=np.float64)[snapshot]
    v = np.asarray(bundle.v, dtype=np.float64)[snapshot]
    w = np.asarray(bundle.w, dtype=np.float64)[snapshot]
    if u.ndim != 3:
        raise ValueError(f"snapshot velocity must be 3D, got {u.shape!r}")
    return u, v, w


def _spectral_derivative(field: np.ndarray, axis: int, kx: np.ndarray, ky: np.ndarray, kz: np.ndarray) -> np.ndarray:
    transformed = np.fft.fftn(field, axes=(0, 1, 2))
    if axis == 0:
        return np.fft.ifftn(1j * kx * transformed, axes=(0, 1, 2)).real
    if axis == 1:
        return np.fft.ifftn(1j * ky * transformed, axes=(0, 1, 2)).real
    if axis == 2:
        return np.fft.ifftn(1j * kz * transformed, axes=(0, 1, 2)).real
    raise ValueError(f"axis must be 0,1,2 got {axis}")


def _lambda2_and_det_from_velocity(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray]:
    if not (u.shape == v.shape == w.shape):
        raise ValueError("velocity component shapes must agree")
    if u.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {u.shape!r}")

    n = int(u.shape[0])
    if int(u.shape[1]) != n or int(u.shape[2]) != n:
        raise ValueError(f"velocity components must be cubic, got {u.shape!r}")
    if n <= 1:
        raise ValueError("velocity grid size must be > 1")

    spacing = domain_length / float(n)
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

    s11 = du_dx
    s22 = dv_dy
    s33 = dw_dz
    s12 = 0.5 * (du_dy + dv_dx)
    s13 = 0.5 * (du_dz + dw_dx)
    s23 = 0.5 * (dv_dz + dw_dy)

    strain = np.empty(u.shape + (3, 3), dtype=np.float64)
    strain[..., 0, 0] = s11
    strain[..., 1, 1] = s22
    strain[..., 2, 2] = s33
    strain[..., 0, 1] = s12
    strain[..., 1, 0] = s12
    strain[..., 0, 2] = s13
    strain[..., 2, 0] = s13
    strain[..., 1, 2] = s23
    strain[..., 2, 1] = s23

    eigenvalues = np.linalg.eigvalsh(strain)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    det_s = np.asarray(np.linalg.det(strain), dtype=np.float64)
    return lambda2, det_s


def _select_cubic_field(value: np.ndarray, *, strict: bool, field_name: str) -> np.ndarray:
    arr = np.asarray(value)
    if arr.ndim == 4:
        if int(arr.shape[0]) != 1:
            raise ValueError(f"{field_name} has unresolved frame axis with shape {arr.shape!r}")
        arr = arr[0]
    if arr.ndim != 3:
        raise ValueError(f"{field_name} must be cubic 3D after extraction, got {arr.shape!r}")
    n = int(arr.shape[0])
    if int(arr.shape[1]) != n or int(arr.shape[2]) != n:
        raise ValueError(f"{field_name} must be cubic, got {arr.shape!r}")
    if strict and not np.all(np.isfinite(arr)):
        raise ValueError(f"{field_name} contains non-finite values")
    return np.asarray(arr, dtype=np.float64)


def _evaluate_frame(
    frame: int,
    snapshot: int,
    raw_bundle: RawBundle,
    eps: float,
    warnings: list[str],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(frame),
        "snapshot_index": int(snapshot),
        "source": str(raw_bundle.path),
        "expected_relation": "lambda2<0 ⇔ det(S)>0 and lambda2>0 ⇔ det(S)<0",
        "lambda2_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
        "det_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
    }

    u, v, w = _raw_velocity_frame(raw_bundle, snapshot)
    l2, det = _lambda2_and_det_from_velocity(u, v, w, raw_bundle.domain_length)
    if l2.shape != det.shape:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"shape mismatch: lambda2={l2.shape!r}, detS={det.shape!r}"]
        return ERROR_STATUS, row

    finite = np.isfinite(l2) & np.isfinite(det)
    cell_count = int(l2.size)
    valid_count = int(np.count_nonzero(finite))
    if valid_count == 0:
        row["status"] = ERROR_STATUS
        row["cell_count"] = cell_count
        row["valid_cell_count"] = 0
        row["errors"] = ["no finite (lambda2, det(S)) pairs"]
        return ERROR_STATUS, row

    if valid_count != cell_count:
        warnings.append(
            f"frame {frame}: excluded {cell_count - valid_count} non-finite (lambda2,det) cells from sign statistics"
        )

    l2_f = l2[finite]
    d_f = det[finite]

    l2_neg, l2_pos, l2_zero = _sign_counts(l2_f, eps)
    det_pos, det_neg, det_zero = _sign_counts(d_f, eps)

    l2_neg_det_nonpos_count = int(np.count_nonzero((l2_f < -eps) & (d_f <= eps)))
    l2_pos_det_nonneg_count = int(np.count_nonzero((l2_f > eps) & (d_f >= -eps)))
    mismatch_count = l2_neg_det_nonpos_count + l2_pos_det_nonneg_count

    lambda2_min, lambda2_max, lambda2_argmin, lambda2_argmax = _minmax_with_location(l2, finite)
    det_min, det_max, det_argmin, det_argmax = _minmax_with_location(det, finite)

    status = OK_STATUS
    if valid_count < cell_count:
        status = PARTIAL_STATUS

    row.update(
        {
            "status": status,
            "cell_count": cell_count,
            "valid_cell_count": valid_count,
            "lambda2_negative_count": l2_neg,
            "lambda2_positive_count": l2_pos,
            "lambda2_zero_count": l2_zero,
            "lambda2_negative_fraction": _fraction(l2_neg, valid_count),
            "lambda2_positive_fraction": _fraction(l2_pos, valid_count),
            "lambda2_zero_fraction": _fraction(l2_zero, valid_count),
            "det_positive_count": det_pos,
            "det_negative_count": det_neg,
            "det_zero_count": det_zero,
            "det_positive_fraction": _fraction(det_pos, valid_count),
            "det_negative_fraction": _fraction(det_neg, valid_count),
            "det_zero_fraction": _fraction(det_zero, valid_count),
            "mismatch_lambda2_negative_det_nonpositive_count": l2_neg_det_nonpos_count,
            "mismatch_lambda2_positive_det_nonnegative_count": l2_pos_det_nonneg_count,
            "mismatch_lambda2_negative_det_nonpositive_fraction": _fraction(l2_neg_det_nonpos_count, valid_count),
            "mismatch_lambda2_positive_det_nonnegative_fraction": _fraction(l2_pos_det_nonneg_count, valid_count),
            "mismatch_count": mismatch_count,
            "mismatch_fraction": _fraction(mismatch_count, valid_count),
            "lambda2_min": lambda2_min,
            "lambda2_max": lambda2_max,
            "lambda2_argmin": lambda2_argmin,
            "lambda2_argmax": lambda2_argmax,
            "det_min": det_min,
            "det_max": det_max,
            "det_argmin": det_argmin,
            "det_argmax": det_argmax,
        }
    )
    return status, row


def _build_aggregate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate: dict[str, Any] = {
        "processed_frames": len(rows),
        "ok_frames": 0,
        "partial_frames": 0,
        "missing_frames": 0,
        "error_frames": 0,
        "global_cell_count": 0,
        "global_valid_cell_count": 0,
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_det_positive_count": 0,
        "global_det_negative_count": 0,
        "global_det_zero_count": 0,
        "global_mismatch_lambda2_negative_det_nonpositive_count": 0,
        "global_mismatch_lambda2_positive_det_nonnegative_count": 0,
        "global_mismatch_count": 0,
        "global_lambda2_min": None,
        "global_lambda2_max": None,
        "global_det_min": None,
        "global_det_max": None,
        "global_lambda2_min_frame": None,
        "global_lambda2_max_frame": None,
        "global_det_min_frame": None,
        "global_det_max_frame": None,
    }

    for row in rows:
        status = row.get("status")
        if status == OK_STATUS:
            aggregate["ok_frames"] += 1
        elif status == PARTIAL_STATUS:
            aggregate["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            aggregate["missing_frames"] += 1
        elif status == ERROR_STATUS:
            aggregate["error_frames"] += 1

        aggregate["global_cell_count"] += int(row.get("cell_count", 0))
        valid_count = int(row.get("valid_cell_count", 0))
        aggregate["global_valid_cell_count"] += valid_count

        for key, agg_key in (
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("det_positive_count", "global_det_positive_count"),
            ("det_negative_count", "global_det_negative_count"),
            ("det_zero_count", "global_det_zero_count"),
            ("mismatch_lambda2_negative_det_nonpositive_count", "global_mismatch_lambda2_negative_det_nonpositive_count"),
            ("mismatch_lambda2_positive_det_nonnegative_count", "global_mismatch_lambda2_positive_det_nonnegative_count"),
            ("mismatch_count", "global_mismatch_count"),
        ):
            aggregate[agg_key] += int(row.get(key, 0))

        lambda2_min = row.get("lambda2_min")
        if isinstance(lambda2_min, (int, float)):
            if aggregate["global_lambda2_min"] is None or lambda2_min < float(aggregate["global_lambda2_min"]):
                aggregate["global_lambda2_min"] = float(lambda2_min)
                aggregate["global_lambda2_min_frame"] = {
                    "frame": row.get("frame"),
                    "snapshot_index": row.get("snapshot_index"),
                    "index": row.get("lambda2_argmin"),
                }
        lambda2_max = row.get("lambda2_max")
        if isinstance(lambda2_max, (int, float)):
            if aggregate["global_lambda2_max"] is None or lambda2_max > float(aggregate["global_lambda2_max"]):
                aggregate["global_lambda2_max"] = float(lambda2_max)
                aggregate["global_lambda2_max_frame"] = {
                    "frame": row.get("frame"),
                    "snapshot_index": row.get("snapshot_index"),
                    "index": row.get("lambda2_argmax"),
                }
        det_min = row.get("det_min")
        if isinstance(det_min, (int, float)):
            if aggregate["global_det_min"] is None or det_min < float(aggregate["global_det_min"]):
                aggregate["global_det_min"] = float(det_min)
                aggregate["global_det_min_frame"] = {
                    "frame": row.get("frame"),
                    "snapshot_index": row.get("snapshot_index"),
                    "index": row.get("det_argmin"),
                }
        det_max = row.get("det_max")
        if isinstance(det_max, (int, float)):
            if aggregate["global_det_max"] is None or det_max > float(aggregate["global_det_max"]):
                aggregate["global_det_max"] = float(det_max)
                aggregate["global_det_max_frame"] = {
                    "frame": row.get("frame"),
                    "snapshot_index": row.get("snapshot_index"),
                    "index": row.get("det_argmax"),
                }

    v = int(aggregate["global_valid_cell_count"])
    aggregate["global_lambda2_positive_fraction"] = _fraction(aggregate["global_lambda2_positive_count"], v)
    aggregate["global_lambda2_negative_fraction"] = _fraction(aggregate["global_lambda2_negative_count"], v)
    aggregate["global_lambda2_zero_fraction"] = _fraction(aggregate["global_lambda2_zero_count"], v)
    aggregate["global_det_positive_fraction"] = _fraction(aggregate["global_det_positive_count"], v)
    aggregate["global_det_negative_fraction"] = _fraction(aggregate["global_det_negative_count"], v)
    aggregate["global_det_zero_fraction"] = _fraction(aggregate["global_det_zero_count"], v)
    aggregate["global_mismatch_lambda2_negative_det_nonpositive_fraction"] = _fraction(
        aggregate["global_mismatch_lambda2_negative_det_nonpositive_count"], v
    )
    aggregate["global_mismatch_lambda2_positive_det_nonnegative_fraction"] = _fraction(
        aggregate["global_mismatch_lambda2_positive_det_nonnegative_count"], v
    )
    aggregate["global_mismatch_fraction"] = _fraction(aggregate["global_mismatch_count"], v)
    return aggregate


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Raw N128 archive path.")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Analyze a single frame index.")
    parser.add_argument("--frame-limit", type=_positive_int, default=None, help="Limit number of frames from t=0.")
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS, help="Signed zero threshold epsilon.")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    if args.zero_eps < 0.0:
        raise ValueError("--zero-eps must be nonnegative")

    warnings: list[str] = []
    errors: list[str] = []

    if not args.raw_archive.exists():
        payload = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "route_decision": ROUTE_DECISION,
            "authority": _authority(),
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "inputs": {
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "zero_eps": float(args.zero_eps),
            },
            "frames": [],
            "aggregate": {
                "processed_frames": 0,
                "ok_frames": 0,
                "partial_frames": 0,
                "missing_frames": 0,
                "error_frames": 1,
            },
            "warnings": [],
            "errors": [f"raw_archive_missing: {args.raw_archive}"],
            "changed_files": [str(args.output)],
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, pretty=args.pretty))
        return 1

    raw_bundle: RawBundle
    try:
        raw_bundle = _load_raw_bundle(args.raw_archive, warnings)
    except Exception as exc:
        payload = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "route_decision": ROUTE_DECISION,
            "authority": _authority(),
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "inputs": {
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "zero_eps": float(args.zero_eps),
            },
            "frames": [],
            "aggregate": {"processed_frames": 0, "ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 1},
            "warnings": warnings,
            "errors": [f"raw_load_failure: {exc}"],
            "changed_files": [str(args.output)],
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, pretty=args.pretty))
        return 1

    frame_indices = list(range(int(raw_bundle.frame_count)))
    if args.frame is not None:
        if args.frame >= int(raw_bundle.frame_count):
            payload = {
                "contract": CONTRACT,
                "status": ERROR_STATUS,
                "route_decision": ROUTE_DECISION,
                "authority": _authority(),
                **CONTROL_CARD,
                "control_card": CONTROL_CARD,
                "inputs": {
                    "raw_archive": str(args.raw_archive),
                    "frame": args.frame,
                    "frame_limit": args.frame_limit,
                    "zero_eps": float(args.zero_eps),
                    "raw_bundle_frame_count": int(raw_bundle.frame_count),
                },
                "frames": [],
                "aggregate": {
                    "processed_frames": 0,
                    "ok_frames": 0,
                    "partial_frames": 0,
                    "missing_frames": 0,
                    "error_frames": 1,
                },
                "warnings": warnings,
                "errors": [f"frame {args.frame} out of range for raw bundle with {raw_bundle.frame_count} frames"],
                "changed_files": [str(args.output)],
            }
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
            print(_json_text(payload, pretty=args.pretty))
            return 1
        frame_indices = [args.frame]

    if args.frame_limit is not None:
        frame_indices = frame_indices[: args.frame_limit]

    rows: list[dict[str, Any]] = []
    frame_statuses: list[str] = []
    for snapshot in frame_indices:
        try:
            status, row = _evaluate_frame(
                frame=int(snapshot),
                snapshot=int(snapshot),
                raw_bundle=raw_bundle,
                eps=float(args.zero_eps),
                warnings=warnings,
            )
        except Exception as exc:
            status = ERROR_STATUS
            row = {
                "frame": int(slot),
                "snapshot_index": int(snapshot),
                "source": str(raw_bundle.path),
                "status": ERROR_STATUS,
                "errors": [f"frame_evaluation_error:{exc}"],
            }
        frame_statuses.append(status)
        rows.append(row)

    aggregate = _build_aggregate(rows)
    status = OK_STATUS
    if not rows:
        status = MISSING_REQUIRED_STATUS
        aggregate["missing_frames"] = aggregate.get("missing_frames", 0) + len(rows)
    elif any(row_status == ERROR_STATUS for row_status in frame_statuses):
        status = ERROR_STATUS
    elif any(row_status == MISSING_REQUIRED_STATUS for row_status in frame_statuses):
        status = PARTIAL_STATUS
    elif any(row_status == PARTIAL_STATUS for row_status in frame_statuses):
        status = PARTIAL_STATUS
    elif warnings:
        status = PARTIAL_STATUS
    if errors:
        status = ERROR_STATUS

    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "raw_bundle_frame_count": int(raw_bundle.frame_count),
            "selected_frames": [int(s) for s in frame_indices],
        },
        "frames": rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": errors,
        "changed_files": [str(args.output)],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 1 if status in {ERROR_STATUS, MISSING_REQUIRED_STATUS} else 0


if __name__ == "__main__":
    raise SystemExit(main())
