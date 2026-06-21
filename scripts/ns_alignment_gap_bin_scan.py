#!/usr/bin/env python3
"""Scan compressive-gap vorticity alignment on the raw N128 velocity archive.

For each reconstructed frame, this script builds strain/eigenframe information and
emits empirical telemetry for the compressive zone `lambda2 >= 0`, grouped by
`delta1 = |lambda1|` thresholds.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_alignment_gap_bin_scan.py"
CONTRACT = "ns_alignment_gap_bin_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_ALIGNMENT_GAP_BIN_SCAN"

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
    "ns_alignment_gap_bin_scan_N128_20260621.json"
)
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_THRESHOLD_VALUES = (0.0, 0.05, 0.10, 0.20, 0.50, 1.0)

CONTROL_CARD = {
    "O": "Scan raw N128 flow fields for compressive-gap vorticity alignment telemetry.",
    "R": (
        "Per-frame reconstruct strain/vorticity, restrict to lambda2 >= 0 (compressive zone), "
        "classify compressive-vs-extensional alignment versus e1/e3, and bin counts by "
        "delta1 = |lambda1| threshold to build a success-vs-gap curve."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed: any malformed frame reconstruction or arithmetic failure degrades to explicit error/missing status.",
    "L": "Load raw archive, reconstruct derivatives, compute eigenframes, emit frame and aggregate telemetry with explicit gap bins.",
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or theorem-promotion claim is inferred by this scan.",
    "F": "Only declared partial/missing/error statuses and explicit diagnostics are permitted; raw reconstruction failure is non-recoverable.",
}

LEGACY_AXIS_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback 6.283185307179586",
)


def _is_benign_warning(value: str) -> bool:
    if not isinstance(value, str):
        return False
    return any(value.endswith(suffix) or value == suffix for suffix in LEGACY_AXIS_WARNING_SUFFIXES)


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


def _parse_thresholds(value: list[float]) -> list[float]:
    ordered: list[float] = []
    seen: set[float] = set()
    for item in value:
        if not math.isfinite(item):
            continue
        threshold = float(item)
        if threshold < 0.0:
            continue
        if threshold in seen:
            continue
        ordered.append(threshold)
        seen.add(threshold)
    ordered.sort()
    return ordered


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


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


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _coerce_float(value: Any, *, name: str | None = None) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name or 'value'} must be finite")
    return parsed


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    if not path.exists():
        raise FileNotFoundError(f"archive missing: {path}")
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in payload:
        try:
            metadata = json.loads(str(payload["meta_json"].item()))
        except Exception:
            metadata = None
        else:
            if isinstance(metadata, dict):
                for key in ("grid_spacing", "dx", "dh", "domain_length", "length", "L", "domain", "N", "N1", "N2", "N3"):
                    if key in metadata and key not in payload:
                        try:
                            payload[key] = np.asarray(metadata[key])
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
            scalar = value.reshape(-1)[0].item()
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


def _infer_domain_length(data: dict[str, np.ndarray], n: int, warnings: list[str]) -> float:
    domain_length, domain_key = _read_scalar_metadata(data, ("domain_length", "length", "L", "domain"))
    if domain_length is not None:
        domain = _coerce_float(domain_length, name=domain_key or "domain_length")
        if domain <= 0.0:
            raise ValueError("domain_length must be positive")
    else:
        domain = None

    spacing, spacing_key = _read_scalar_metadata(data, ("grid_spacing", "dx", "dh"))
    if spacing is not None:
        spacing_value = _coerce_float(spacing, name=spacing_key or "grid_spacing")
        if spacing_value <= 0.0:
            raise ValueError("grid_spacing must be positive")
        if domain is None:
            domain = float(spacing_value * n)
        elif not math.isclose(domain, spacing_value * n, rel_tol=1e-8, abs_tol=1e-8):
            warnings.append(
                f"domain_length/grid_spacing mismatch: {domain} vs {spacing_value * n} (using domain_length)"
            )

    if domain is not None:
        return domain
    fallback = 2.0 * math.pi
    warnings.append(f"domain_length unavailable; using fallback {fallback}")
    return fallback


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
            warnings.append("velocity_snapshots last-axis layout detected")
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
            warnings.append("velocity fallback axis-1 channel layout detected")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity fallback trailing channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"unsupported fallback velocity shape {velocity.shape!r}")

    raise ValueError("no raw velocity components found")


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
            raise ValueError(f"snapshot velocity must be 3D, got {u.shape!r}")
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


def _strain_and_vorticity_from_velocity(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if not (u.shape == v.shape == w.shape):
        raise ValueError("velocity component shapes must agree")
    if u.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {u.shape!r}")
    n = int(u.shape[0])
    if int(u.shape[1]) != n or int(u.shape[2]) != n:
        raise ValueError(f"velocity component shape must be cubic, got {u.shape!r}")
    if n <= 1:
        raise ValueError("velocity grid size must be > 1")
    if not math.isfinite(float(domain_length)) or float(domain_length) <= 0.0:
        raise ValueError("domain_length must be finite positive")

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

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    lambda1 = np.asarray(eigenvalues[..., 0], dtype=np.float64)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    lambda3 = np.asarray(eigenvalues[..., 2], dtype=np.float64)
    e1 = np.asarray(eigenvectors[..., :, 0], dtype=np.float64)
    e3 = np.asarray(eigenvectors[..., :, 2], dtype=np.float64)

    omega_x = dw_dy - dv_dz
    omega_y = du_dz - dw_dx
    omega_z = dv_dx - du_dy
    omega_norm_sq = omega_x * omega_x + omega_y * omega_y + omega_z * omega_z
    return lambda1, lambda2, lambda3, e1, e3, omega_x, omega_y, omega_z, omega_norm_sq


def _sign_counts(values: np.ndarray, eps: float) -> tuple[int, int, int]:
    pos = int(np.count_nonzero(values > eps))
    neg = int(np.count_nonzero(values < -eps))
    zero = int(values.size - pos - neg)
    return pos, neg, zero


def _align_counts(
    align_sq_a: np.ndarray,
    align_sq_b: np.ndarray,
    eps: float,
) -> tuple[int, int, int]:
    a_count = int(np.count_nonzero(align_sq_a > align_sq_b + eps))
    b_count = int(np.count_nonzero(align_sq_b > align_sq_a + eps))
    tie_count = int(align_sq_a.size - a_count - b_count)
    return a_count, b_count, tie_count


def _empty_gap_row(threshold: float) -> dict[str, Any]:
    return {
        "delta1_threshold": float(threshold),
        "cell_count": 0,
        "align_e1_count": 0,
        "align_e3_count": 0,
        "align_tie_count": 0,
        "align_success_count": 0,
        "align_mismatch_count": 0,
        "align_e1_fraction": 0.0,
        "align_e3_fraction": 0.0,
        "align_tie_fraction": 0.0,
        "align_success_fraction": 0.0,
        "align_mismatch_fraction": 0.0,
        "align_zone_fraction": 0.0,
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: RawBundle,
    eps: float,
    thresholds: list[float],
    warnings: list[str],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "lambda2_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
        "vorticity_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
    }

    u, v, w = _raw_velocity_frame(bundle, snapshot)
    lambda1, lambda2, _lambda3, e1, e3, omega_x, omega_y, omega_z, omega_norm_sq = _strain_and_vorticity_from_velocity(
        u, v, w, bundle.domain_length
    )
    if lambda2.shape != lambda1.shape or e1.shape[:3] != lambda2.shape or e3.shape[:3] != lambda2.shape:
        row["status"] = ERROR_STATUS
        row["errors"] = ["reconstructed shape mismatch"]
        return ERROR_STATUS, row

    finite = (
        np.isfinite(lambda1)
        & np.isfinite(lambda2)
        & np.isfinite(e1).all(axis=-1)
        & np.isfinite(e3).all(axis=-1)
        & np.isfinite(omega_x)
        & np.isfinite(omega_y)
        & np.isfinite(omega_z)
        & np.isfinite(omega_norm_sq)
    )
    cell_count = int(lambda2.size)
    finite_count = int(np.count_nonzero(finite))
    row["cell_count"] = cell_count
    row["finite_cell_count"] = finite_count
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite reconstructed fields"]
        return ERROR_STATUS, row
    if finite_count != cell_count:
        warnings.append(f"frame {slot}: excluded {cell_count - finite_count} non-finite reconstructed cells")

    lambda2_f = np.asarray(lambda2[finite], dtype=np.float64)
    l2_pos, l2_neg, l2_zero = _sign_counts(lambda2_f, eps)
    compressive_mask = finite & (lambda2 >= 0.0)
    compressive_zone_count = int(np.count_nonzero(compressive_mask))
    row["lambda2_positive_count"] = l2_pos
    row["lambda2_negative_count"] = l2_neg
    row["lambda2_zero_count"] = l2_zero
    row["lambda2_positive_fraction"] = _fraction(l2_pos, finite_count)
    row["lambda2_negative_fraction"] = _fraction(l2_neg, finite_count)
    row["lambda2_zero_fraction"] = _fraction(l2_zero, finite_count)
    row["compressive_zone_cell_count"] = compressive_zone_count

    if compressive_zone_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["alignable_zone_cell_count"] = 0
        row["align_e1_count"] = 0
        row["align_e3_count"] = 0
        row["align_tie_count"] = 0
        row["align_rule_success_count"] = 0
        row["align_rule_mismatch_count"] = 0
        row["align_e1_fraction"] = 0.0
        row["align_e3_fraction"] = 0.0
        row["align_tie_fraction"] = 0.0
        row["align_rule_success_fraction"] = 0.0
        row["align_rule_mismatch_fraction"] = 0.0
        row["delta1_sum"] = 0.0
        row["delta1_min"] = None
        row["delta1_max"] = None
        row["delta1_mean"] = 0.0
        row["gap_threshold_rows"] = [_empty_gap_row(threshold) for threshold in thresholds]
        row["errors"] = ["no finite compressive-zone cells (lambda2 >= 0)"]
        return MISSING_REQUIRED_STATUS, row

    alignable_mask = compressive_mask & (omega_norm_sq > eps)
    alignable_zone_count = int(np.count_nonzero(alignable_mask))
    row["alignable_zone_cell_count"] = alignable_zone_count
    if alignable_zone_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["align_e1_count"] = 0
        row["align_e3_count"] = 0
        row["align_tie_count"] = 0
        row["align_rule_success_count"] = 0
        row["align_rule_mismatch_count"] = 0
        row["align_e1_fraction"] = 0.0
        row["align_e3_fraction"] = 0.0
        row["align_tie_fraction"] = 0.0
        row["align_rule_success_fraction"] = 0.0
        row["align_rule_mismatch_fraction"] = 0.0
        row["delta1_sum"] = 0.0
        row["delta1_min"] = None
        row["delta1_max"] = None
        row["delta1_mean"] = 0.0
        row["gap_threshold_rows"] = [_empty_gap_row(threshold) for threshold in thresholds]
        row["errors"] = ["no nonzero-vorticity cells in compressive zone"]
        return MISSING_REQUIRED_STATUS, row

    delta1 = np.abs(lambda1[alignable_mask])
    omega_norm = np.sqrt(np.maximum(omega_norm_sq[alignable_mask], 0.0))
    e1_masked = e1[alignable_mask]
    e3_masked = e3[alignable_mask]

    align_e1 = (
        (omega_x[alignable_mask] * e1_masked[:, 0])
        + (omega_y[alignable_mask] * e1_masked[:, 1])
        + (omega_z[alignable_mask] * e1_masked[:, 2])
    ) / omega_norm
    align_e3 = (
        (omega_x[alignable_mask] * e3_masked[:, 0])
        + (omega_y[alignable_mask] * e3_masked[:, 1])
        + (omega_z[alignable_mask] * e3_masked[:, 2])
    ) / omega_norm
    align_e1_sq = align_e1 * align_e1
    align_e3_sq = align_e3 * align_e3

    if np.any(np.isnan(align_e1_sq)) or np.any(np.isnan(align_e3_sq)):
        row["status"] = ERROR_STATUS
        row["errors"] = ["alignment computation produced NaN"]
        return ERROR_STATUS, row

    if np.any(align_e1_sq < -1.0e-12) or np.any(align_e1_sq > 1.0 + 1.0e-12):
        warnings.append(f"frame {slot}: align_e1_sq out of [0,1]")
    if np.any(align_e3_sq < -1.0e-12) or np.any(align_e3_sq > 1.0 + 1.0e-12):
        warnings.append(f"frame {slot}: align_e3_sq out of [0,1]")

    align_e1_count, align_e3_count, align_tie_count = _align_counts(align_e1_sq, align_e3_sq, eps)
    align_rule_success_count = int(align_e1_count + align_e3_count)
    align_rule_mismatch_count = int(align_tie_count)

    row["align_e1_count"] = align_e1_count
    row["align_e3_count"] = align_e3_count
    row["align_tie_count"] = align_tie_count
    row["align_rule_success_count"] = align_rule_success_count
    row["align_rule_mismatch_count"] = align_rule_mismatch_count
    row["align_e1_fraction"] = _fraction(align_e1_count, alignable_zone_count)
    row["align_e3_fraction"] = _fraction(align_e3_count, alignable_zone_count)
    row["align_tie_fraction"] = _fraction(align_tie_count, alignable_zone_count)
    row["align_rule_success_fraction"] = _fraction(align_rule_success_count, alignable_zone_count)
    row["align_rule_mismatch_fraction"] = _fraction(align_rule_mismatch_count, alignable_zone_count)

    delta1_sum = float(np.sum(delta1))
    delta1_min = float(np.min(delta1))
    delta1_max = float(np.max(delta1))
    row["delta1_sum"] = delta1_sum
    row["delta1_min"] = delta1_min
    row["delta1_max"] = delta1_max
    row["delta1_mean"] = delta1_sum / float(alignable_zone_count) if alignable_zone_count > 0 else 0.0

    gap_rows: list[dict[str, Any]] = []
    for threshold in thresholds:
        gap_mask = delta1 >= float(threshold)
        gap_count = int(np.count_nonzero(gap_mask))
        if gap_count == 0:
            gap_rows.append(
                {
                    "delta1_threshold": float(threshold),
                    "cell_count": 0,
                    "align_e1_count": 0,
                    "align_e3_count": 0,
                    "align_tie_count": 0,
                    "align_success_count": 0,
                    "align_mismatch_count": 0,
                    "align_e1_fraction": 0.0,
                    "align_e3_fraction": 0.0,
                    "align_tie_fraction": 0.0,
                    "align_success_fraction": 0.0,
                    "align_mismatch_fraction": 0.0,
                    "align_zone_fraction": 0.0,
                }
            )
            continue

        idx = np.nonzero(gap_mask)[0]
        a_sq = align_e1_sq[idx]
        b_sq = align_e3_sq[idx]
        e1_count, e3_count, tie_count = _align_counts(a_sq, b_sq, eps)
        success_count = int(e1_count + e3_count)
        mismatch_count = int(tie_count)
        gap_rows.append(
            {
                "delta1_threshold": float(threshold),
                "cell_count": int(gap_count),
                "align_e1_count": int(e1_count),
                "align_e3_count": int(e3_count),
                "align_tie_count": int(tie_count),
                "align_success_count": int(success_count),
                "align_mismatch_count": int(mismatch_count),
                "align_e1_fraction": _fraction(e1_count, gap_count),
                "align_e3_fraction": _fraction(e3_count, gap_count),
                "align_tie_fraction": _fraction(tie_count, gap_count),
                "align_success_fraction": _fraction(success_count, gap_count),
                "align_mismatch_fraction": _fraction(mismatch_count, gap_count),
                "align_zone_fraction": _fraction(gap_count, alignable_zone_count),
            }
        )
    row["gap_threshold_rows"] = gap_rows

    status = OK_STATUS
    if finite_count < cell_count:
        status = PARTIAL_STATUS
    row["status"] = status
    return status, row


def _build_aggregate(rows: list[dict[str, Any]], thresholds: list[float]) -> dict[str, Any]:
    aggregate: dict[str, Any] = {
        "processed_frames": int(len(rows)),
        "ok_frames": 0,
        "partial_frames": 0,
        "missing_frames": 0,
        "error_frames": 0,
        "global_cell_count": 0,
        "global_finite_cell_count": 0,
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_compressive_zone_cell_count": 0,
        "global_alignable_zone_cell_count": 0,
        "global_align_e1_count": 0,
        "global_align_e3_count": 0,
        "global_align_tie_count": 0,
        "global_align_rule_success_count": 0,
        "global_align_rule_mismatch_count": 0,
        "global_delta1_sum": 0.0,
        "global_delta1_min": None,
        "global_delta1_max": None,
    }

    threshold_rows: dict[float, dict[str, Any]] = {
        float(threshold): _empty_gap_row(float(threshold)) for threshold in thresholds
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
        else:
            aggregate["error_frames"] += 1

        aggregate["global_cell_count"] += int(row.get("cell_count", 0))
        aggregate["global_finite_cell_count"] += int(row.get("finite_cell_count", 0))
        for row_key, agg_key in (
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("compressive_zone_cell_count", "global_compressive_zone_cell_count"),
            ("alignable_zone_cell_count", "global_alignable_zone_cell_count"),
            ("align_e1_count", "global_align_e1_count"),
            ("align_e3_count", "global_align_e3_count"),
            ("align_tie_count", "global_align_tie_count"),
            ("align_rule_success_count", "global_align_rule_success_count"),
            ("align_rule_mismatch_count", "global_align_rule_mismatch_count"),
        ):
            aggregate[agg_key] += int(row.get(row_key, 0))

        aggregate["global_delta1_sum"] += float(row.get("delta1_sum", 0.0))

        delta1_min = row.get("delta1_min")
        if isinstance(delta1_min, (int, float)) and math.isfinite(float(delta1_min)):
            if aggregate["global_delta1_min"] is None or float(delta1_min) < float(aggregate["global_delta1_min"]):
                aggregate["global_delta1_min"] = float(delta1_min)
        delta1_max = row.get("delta1_max")
        if isinstance(delta1_max, (int, float)) and math.isfinite(float(delta1_max)):
            if aggregate["global_delta1_max"] is None or float(delta1_max) > float(aggregate["global_delta1_max"]):
                aggregate["global_delta1_max"] = float(delta1_max)

        for entry in row.get("gap_threshold_rows", []) if isinstance(row.get("gap_threshold_rows"), list) else []:
            threshold_raw = entry.get("delta1_threshold")
            try:
                threshold = float(threshold_raw)  # type: ignore[arg-type]
            except (TypeError, ValueError):
                continue
            if not math.isfinite(threshold) or threshold < 0.0:
                continue
            stats = threshold_rows.get(float(threshold))
            if stats is None:
                threshold_rows[float(threshold)] = _empty_gap_row(float(threshold))
                stats = threshold_rows[float(threshold)]
            stats["cell_count"] += int(entry.get("cell_count", 0))
            stats["align_e1_count"] += int(entry.get("align_e1_count", 0))
            stats["align_e3_count"] += int(entry.get("align_e3_count", 0))
            stats["align_tie_count"] += int(entry.get("align_tie_count", 0))
            stats["align_success_count"] += int(entry.get("align_success_count", 0))
            stats["align_mismatch_count"] += int(entry.get("align_mismatch_count", 0))

    align_region = int(aggregate["global_alignable_zone_cell_count"])
    aggregate["global_lambda2_positive_fraction"] = _fraction(aggregate["global_lambda2_positive_count"], aggregate["global_finite_cell_count"])
    aggregate["global_lambda2_negative_fraction"] = _fraction(aggregate["global_lambda2_negative_count"], aggregate["global_finite_cell_count"])
    aggregate["global_lambda2_zero_fraction"] = _fraction(aggregate["global_lambda2_zero_count"], aggregate["global_finite_cell_count"])
    aggregate["global_compressive_zone_fraction"] = _fraction(aggregate["global_compressive_zone_cell_count"], aggregate["global_finite_cell_count"])
    aggregate["global_align_e1_fraction"] = _fraction(aggregate["global_align_e1_count"], align_region)
    aggregate["global_align_e3_fraction"] = _fraction(aggregate["global_align_e3_count"], align_region)
    aggregate["global_align_tie_fraction"] = _fraction(aggregate["global_align_tie_count"], align_region)
    aggregate["global_align_rule_success_fraction"] = _fraction(aggregate["global_align_rule_success_count"], align_region)
    aggregate["global_align_rule_mismatch_fraction"] = _fraction(aggregate["global_align_rule_mismatch_count"], align_region)
    aggregate["global_delta1_mean"] = _fraction(aggregate["global_delta1_sum"], align_region)

    for threshold, stats in threshold_rows.items():
        cell_count = int(stats["cell_count"])
        stats["align_e1_fraction"] = _fraction(int(stats["align_e1_count"]), cell_count)
        stats["align_e3_fraction"] = _fraction(int(stats["align_e3_count"]), cell_count)
        stats["align_tie_fraction"] = _fraction(int(stats["align_tie_count"]), cell_count)
        stats["align_success_fraction"] = _fraction(int(stats["align_success_count"]), cell_count)
        stats["align_mismatch_fraction"] = _fraction(int(stats["align_mismatch_count"]), cell_count)
        stats["align_zone_fraction"] = _fraction(cell_count, align_region)

    aggregate["gap_threshold_rows"] = [
        {
            "delta1_threshold": threshold,
            "cell_count": int(entry["cell_count"]),
            "align_e1_count": int(entry["align_e1_count"]),
            "align_e3_count": int(entry["align_e3_count"]),
            "align_tie_count": int(entry["align_tie_count"]),
            "align_success_count": int(entry["align_success_count"]),
            "align_mismatch_count": int(entry["align_mismatch_count"]),
            "align_zone_fraction": float(entry["align_zone_fraction"]),
            "align_e1_fraction": float(entry["align_e1_fraction"]),
            "align_e3_fraction": float(entry["align_e3_fraction"]),
            "align_tie_fraction": float(entry["align_tie_fraction"]),
            "align_success_fraction": float(entry["align_success_fraction"]),
            "align_mismatch_fraction": float(entry["align_mismatch_fraction"]),
        }
        for threshold, entry in sorted(threshold_rows.items(), key=lambda item: item[0])
    ]

    aggregate["gap_threshold_success_curve"] = [
        {
            "delta1_threshold": entry["delta1_threshold"],
            "success_fraction": entry["align_success_fraction"],
            "mismatch_fraction": entry["align_mismatch_fraction"],
        }
        for entry in aggregate["gap_threshold_rows"]
    ]
    return aggregate


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Raw N128 archive")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Process a single frame index.")
    parser.add_argument(
        "--frame-limit",
        type=_positive_int,
        default=None,
        help="Maximum number of frames processed from the archive.",
    )
    parser.add_argument(
        "--zero-eps",
        type=float,
        default=DEFAULT_ZERO_EPS,
        help="Signed-zero threshold for alignments and eigenvalue sign counts.",
    )
    parser.add_argument(
        "--delta1-thresholds",
        type=float,
        nargs="+",
        default=list(DEFAULT_THRESHOLD_VALUES),
        help="Bin thresholds for delta1 = |lambda1| on compressive-zone alignment cells.",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _build_error_payload(path: Path, errors: list[str]) -> dict[str, Any]:
    return {
        "contract": CONTRACT,
        "status": ERROR_STATUS,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        **CONTROL_CARD,
        "script": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "inputs": {},
        "frames": [],
        "aggregate": {
            "processed_frames": 0,
            "ok_frames": 0,
            "partial_frames": 0,
            "missing_frames": 0,
            "error_frames": 1,
        },
        "warnings": [],
        "errors": errors,
        "changed_files": [str(path)],
    }


def main() -> int:
    args = _parse_args()
    if args.zero_eps < 0.0:
        raise ValueError("--zero-eps must be nonnegative")

    thresholds = _parse_thresholds(list(args.delta1_thresholds))
    if not thresholds:
        payload = _build_error_payload(args.output, ["delta1-threshold list is empty after parsing"])
        payload["inputs"] = {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "delta1_thresholds": [],
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, pretty=args.pretty))
        return 1

    warnings: list[str] = []
    errors: list[str] = []

    if not args.raw_archive.exists():
        payload = _build_error_payload(args.output, [f"raw_archive_missing: {args.raw_archive}"])
        payload["inputs"] = {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "delta1_thresholds": thresholds,
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, pretty=args.pretty))
        return 1

    try:
        bundle = _load_raw_bundle(args.raw_archive, warnings)
    except Exception as exc:
        payload = _build_error_payload(args.output, [f"raw_load_failure: {exc}"])
        payload["inputs"] = {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "delta1_thresholds": thresholds,
        }
        payload["warnings"] = warnings
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, pretty=args.pretty))
        return 1

    frame_indices = list(range(int(bundle.frame_count)))
    if args.frame is not None:
        if args.frame >= int(bundle.frame_count):
            payload = _build_error_payload(
                args.output,
                [f"requested frame {args.frame} out of range for {bundle.frame_count} frames"],
            )
            payload["inputs"] = {
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "zero_eps": float(args.zero_eps),
                "delta1_thresholds": thresholds,
            }
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
            print(_json_text(payload, pretty=args.pretty))
            return 1
        frame_indices = [args.frame]
    if args.frame_limit is not None:
        frame_indices = frame_indices[: int(args.frame_limit)]

    rows: list[dict[str, Any]] = []
    row_statuses: list[str] = []
    for slot in frame_indices:
        try:
            status, row = _evaluate_frame(
                slot=int(slot),
                snapshot=int(slot),
                bundle=bundle,
                eps=float(args.zero_eps),
                thresholds=thresholds,
                warnings=warnings,
            )
        except Exception as exc:
            status = ERROR_STATUS
            row = {
                "frame": int(slot),
                "snapshot_index": int(slot),
                "source": str(bundle.path),
                "status": ERROR_STATUS,
                "errors": [f"frame_evaluation_error:{exc}"],
            }
        rows.append(row)
        row_statuses.append(str(status))

    aggregate = _build_aggregate(rows, thresholds)
    if not rows:
        status = MISSING_REQUIRED_STATUS
    elif ERROR_STATUS in row_statuses:
        status = ERROR_STATUS
    elif MISSING_REQUIRED_STATUS in row_statuses:
        status = MISSING_REQUIRED_STATUS
    elif PARTIAL_STATUS in row_statuses:
        status = PARTIAL_STATUS
    elif any(not _is_benign_warning(warning) for warning in warnings):
        status = PARTIAL_STATUS
    else:
        status = OK_STATUS

    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        **CONTROL_CARD,
        "script": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "delta1_thresholds": thresholds,
            "selected_frames": [int(frame) for frame in frame_indices],
            "raw_bundle_frame_count": int(bundle.frame_count),
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
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
