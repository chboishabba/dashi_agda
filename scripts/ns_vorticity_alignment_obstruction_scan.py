#!/usr/bin/env python3
"""Scan compressive-dominant vorticity alignment on the raw N128 velocity archive."""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_vorticity_alignment_obstruction_scan.py"
CONTRACT = "ns_vorticity_alignment_obstruction_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_VORTICITY_ALIGNMENT_OBSTRUCTION_SCAN"

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
    "ns_vorticity_alignment_obstruction_scan_N128_20260621.json"
)

DEFAULT_ZERO_EPS = 1.0e-12

CONTROL_CARD = {
    "O": "Measure compressive-vs-extensional vorticity alignment on raw N128 snapshots.",
    "R": (
        "Reconstruct strain, vorticity, and strain eigenframes from raw velocity; "
        "compute lambda2-sign/coverage and omega alignment telemetry against e1/e3 in lambda2>=0."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical scan: no raw data reconstruction or inconsistent payloads are promoted.",
    "L": "Reconstruct from raw velocity per frame, compute per-cell eigenvectors, and emit frame/aggregate telemetry.",
    "P": ROUTE_DECISION,
    "G": "No theorem/clay promotion is inferred by this script.",
    "F": "Only explicit frame-level data deficiencies are treated as partial/missing; missing raw archive is an error.",
}


LEGACY_AXIS_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis channel layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback",
)


def _is_benign_warning(value: str) -> bool:
    if not isinstance(value, str):
        return False
    return any(suffix in value for suffix in LEGACY_AXIS_WARNING_SUFFIXES)


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


def _coerce_float(value: Any, *, finite: bool = True, name: str | None = None) -> float:
    parsed = float(value)
    if finite and not math.isfinite(parsed):
        raise ValueError(f"{name or 'value'} must be finite")
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


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


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
                for key in ("grid_spacing", "dx", "domain_length", "length", "L", "domain", "N", "N1", "N2", "N3"):
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


def _frame_sort_key(path: Path) -> tuple[int, str]:
    stem = path.stem.lower()
    match = re.search(r"(?:^|[_-])(frame|snapshot)[_-]?(\d+)(?:$|[_-])", stem)
    if match is not None:
        return int(match.group(2)), path.name
    match = re.search(r"(?:^|[_-])(\d+)(?:$|[_-])", stem)
    if match is not None:
        return int(match.group(1)), path.name
    return 10**12, path.name


def _sign_counts(values: np.ndarray, eps: float) -> tuple[int, int, int]:
    pos = int(np.count_nonzero(values > eps))
    neg = int(np.count_nonzero(values < -eps))
    zero = int(values.size - pos - neg)
    return pos, neg, zero


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


def _strain_eigen_and_vorticity_from_velocity(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if not (u.shape == v.shape == w.shape):
        raise ValueError("velocity component shapes must agree")
    if u.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {u.shape!r}")
    if int(u.shape[0]) <= 1:
        raise ValueError("velocity grid size must be >1")

    n = int(u.shape[0])
    if int(u.shape[1]) != n or int(u.shape[2]) != n:
        raise ValueError(f"velocity components must be cubic, got {u.shape!r}")

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

    omega_x = dw_dy - dv_dz
    omega_y = du_dz - dw_dx
    omega_z = dv_dx - du_dy
    omega_norm_sq = omega_x * omega_x + omega_y * omega_y + omega_z * omega_z

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)

    e1 = np.asarray(eigenvectors[..., :, 0], dtype=np.float64)
    e3 = np.asarray(eigenvectors[..., :, 2], dtype=np.float64)
    return lambda2, e1, e3, omega_x, omega_y, omega_z, omega_norm_sq


def _evaluate_frame(
    slot: int,
    snapshot: int,
    raw_bundle: RawBundle,
    eps: float,
    warnings: list[str],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(raw_bundle.path),
        "expected_relation": "no-vs-e3_alignment_telemetry_only",
        "lambda2_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
        "vorticity_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
    }

    u, v, w = _raw_velocity_frame(raw_bundle, snapshot)
    lambda2, e1, e3, omega_x, omega_y, omega_z, omega_norm_sq = _strain_eigen_and_vorticity_from_velocity(
        u,
        v,
        w,
        raw_bundle.domain_length,
    )
    if e1.shape[:3] != lambda2.shape or omega_x.shape != lambda2.shape:
        row["status"] = ERROR_STATUS
        row["errors"] = ["reconstructed fields shape mismatch"]
        return ERROR_STATUS, row

    finite = (
        np.isfinite(lambda2)
        & np.isfinite(e1).all(axis=-1)
        & np.isfinite(e3).all(axis=-1)
        & np.isfinite(omega_x)
        & np.isfinite(omega_y)
        & np.isfinite(omega_z)
        & np.isfinite(omega_norm_sq)
    )
    cell_count = int(lambda2.size)
    finite_count = int(np.count_nonzero(finite))
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["cell_count"] = cell_count
        row["errors"] = ["no finite reconstructed fields"]
        return ERROR_STATUS, row

    if finite_count != cell_count:
        warnings.append(
            f"frame {slot}: excluded {cell_count - finite_count} non-finite (lambda2/eigenvector/vorticity) cells"
        )

    lambda2_f = lambda2[finite]
    l2_pos, l2_neg, l2_zero = _sign_counts(lambda2_f, eps)

    region_mask = finite & (lambda2 >= 0.0)
    region_count = int(np.count_nonzero(region_mask))
    if region_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["cell_count"] = cell_count
        row["finite_cell_count"] = finite_count
        row["lambda2_positive_count"] = l2_pos
        row["lambda2_negative_count"] = l2_neg
        row["lambda2_zero_count"] = l2_zero
        row["lambda2_positive_fraction"] = _fraction(l2_pos, finite_count)
        row["lambda2_negative_fraction"] = _fraction(l2_neg, finite_count)
        row["lambda2_zero_fraction"] = _fraction(l2_zero, finite_count)
        row["lambda2_region_cell_count"] = 0
        row["alignment_region_cell_count"] = 0
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
        row["align_e1_sq_sum"] = 0.0
        row["align_e3_sq_sum"] = 0.0
        row["align_e1_sq_min"] = None
        row["align_e1_sq_max"] = None
        row["align_e3_sq_min"] = None
        row["align_e3_sq_max"] = None
        row["errors"] = ["no finite lambda2>=0 cells for alignment telemetry"]
        return MISSING_REQUIRED_STATUS, row

    region_epsilon = max(eps, 0.0)
    region_mask = region_mask & (omega_norm_sq > eps)
    region_count = int(np.count_nonzero(region_mask))
    if region_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["cell_count"] = cell_count
        row["finite_cell_count"] = finite_count
        row["lambda2_positive_count"] = l2_pos
        row["lambda2_negative_count"] = l2_neg
        row["lambda2_zero_count"] = l2_zero
        row["lambda2_positive_fraction"] = _fraction(l2_pos, finite_count)
        row["lambda2_negative_fraction"] = _fraction(l2_neg, finite_count)
        row["lambda2_zero_fraction"] = _fraction(l2_zero, finite_count)
        row["lambda2_region_cell_count"] = int(np.count_nonzero(finite & (lambda2 >= 0.0)))
        row["alignment_region_cell_count"] = 0
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
        row["align_e1_sq_sum"] = 0.0
        row["align_e3_sq_sum"] = 0.0
        row["align_e1_sq_min"] = None
        row["align_e3_sq_min"] = None
        row["align_e1_sq_max"] = None
        row["align_e3_sq_max"] = None
        row["errors"] = ["no finite, nonzero-vorticity cells in lambda2>=0 mask"]
        return MISSING_REQUIRED_STATUS, row

    omega_x_masked = omega_x[region_mask]
    omega_y_masked = omega_y[region_mask]
    omega_z_masked = omega_z[region_mask]
    omega_norm_masked = np.sqrt(np.maximum(omega_norm_sq[region_mask], 0.0))

    e1_masked = e1[region_mask]
    e3_masked = e3[region_mask]
    e1x = e1_masked[:, 0]
    e1y = e1_masked[:, 1]
    e1z = e1_masked[:, 2]
    e3x = e3_masked[:, 0]
    e3y = e3_masked[:, 1]
    e3z = e3_masked[:, 2]

    align_e1 = (
        (omega_x_masked * e1x + omega_y_masked * e1y + omega_z_masked * e1z) / omega_norm_masked
    )
    align_e3 = (
        (omega_x_masked * e3x + omega_y_masked * e3y + omega_z_masked * e3z) / omega_norm_masked
    )
    align_e1_sq = align_e1 * align_e1
    align_e3_sq = align_e3 * align_e3

    if np.any(np.isnan(align_e1_sq)) or np.any(np.isnan(align_e3_sq)):
        row["status"] = ERROR_STATUS
        row["cell_count"] = cell_count
        row["finite_cell_count"] = finite_count
        row["errors"] = ["alignment produced NaN values"]
        return ERROR_STATUS, row

    if np.any(align_e1_sq < -1.0e-12) or np.any(align_e1_sq > 1.0 + 1.0e-12):
        warnings.append(f"frame {slot}: align_e1_sq out of [0,1]")
    if np.any(align_e3_sq < -1.0e-12) or np.any(align_e3_sq > 1.0 + 1.0e-12):
        warnings.append(f"frame {slot}: align_e3_sq out of [0,1]")

    align_e1_count = int(np.count_nonzero(align_e1_sq > align_e3_sq + eps))
    align_e3_count = int(np.count_nonzero(align_e3_sq > align_e1_sq + eps))
    align_tie_count = int(region_count - align_e1_count - align_e3_count)
    if align_tie_count < 0:
        align_tie_count = int(region_count) - align_e1_count - align_e3_count

    align_e1_sq_sum = float(np.sum(align_e1_sq))
    align_e3_sq_sum = float(np.sum(align_e3_sq))
    align_e1_sq_min = float(np.min(align_e1_sq))
    align_e1_sq_max = float(np.max(align_e1_sq))
    align_e3_sq_min = float(np.min(align_e3_sq))
    align_e3_sq_max = float(np.max(align_e3_sq))
    align_e1_sq_mean = _fraction(align_e1_sq_sum, region_count) if region_count else 0.0
    align_e3_sq_mean = _fraction(align_e3_sq_sum, region_count) if region_count else 0.0
    align_rule_success_count = int(align_e1_count + align_e3_count)

    status = OK_STATUS
    if finite_count < cell_count:
        status = PARTIAL_STATUS
    row.update(
        {
            "status": status,
            "cell_count": cell_count,
            "finite_cell_count": finite_count,
            "lambda2_positive_count": l2_pos,
            "lambda2_negative_count": l2_neg,
            "lambda2_zero_count": l2_zero,
            "lambda2_positive_fraction": _fraction(l2_pos, finite_count),
            "lambda2_negative_fraction": _fraction(l2_neg, finite_count),
            "lambda2_zero_fraction": _fraction(l2_zero, finite_count),
            "lambda2_region_cell_count": int(np.count_nonzero(finite & (lambda2 >= 0.0))),
            "alignment_region_cell_count": region_count,
            "align_e1_count": align_e1_count,
            "align_e3_count": align_e3_count,
            "align_tie_count": align_tie_count,
            "align_e1_fraction": _fraction(align_e1_count, region_count),
            "align_e3_fraction": _fraction(align_e3_count, region_count),
            "align_tie_fraction": _fraction(align_tie_count, region_count),
            "align_rule_success_count": align_rule_success_count,
            "align_rule_mismatch_count": align_tie_count,
            "align_rule_success_fraction": _fraction(align_rule_success_count, region_count),
            "align_rule_mismatch_fraction": _fraction(align_tie_count, region_count),
            "align_e1_sq_sum": align_e1_sq_sum,
            "align_e3_sq_sum": align_e3_sq_sum,
            "align_e1_sq_mean": align_e1_sq_mean,
            "align_e3_sq_mean": align_e3_sq_mean,
            "align_e1_sq_min": align_e1_sq_min,
            "align_e1_sq_max": align_e1_sq_max,
            "align_e3_sq_min": align_e3_sq_min,
            "align_e3_sq_max": align_e3_sq_max,
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
        "global_finite_cell_count": 0,
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_lambda2_region_cell_count": 0,
        "global_alignment_region_cell_count": 0,
        "global_align_e1_count": 0,
        "global_align_e3_count": 0,
        "global_align_tie_count": 0,
        "global_align_rule_success_count": 0,
        "global_align_rule_mismatch_count": 0,
        "global_align_e1_sq_sum": 0.0,
        "global_align_e3_sq_sum": 0.0,
        "global_align_e1_sq_min": None,
        "global_align_e1_sq_max": None,
        "global_align_e3_sq_min": None,
        "global_align_e3_sq_max": None,
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
        aggregate["global_finite_cell_count"] += int(row.get("finite_cell_count", 0))
        for row_key, agg_key in (
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("lambda2_region_cell_count", "global_lambda2_region_cell_count"),
            ("alignment_region_cell_count", "global_alignment_region_cell_count"),
            ("align_e1_count", "global_align_e1_count"),
            ("align_e3_count", "global_align_e3_count"),
            ("align_tie_count", "global_align_tie_count"),
            ("align_rule_success_count", "global_align_rule_success_count"),
            ("align_rule_mismatch_count", "global_align_rule_mismatch_count"),
        ):
            aggregate[agg_key] += int(row.get(row_key, 0))
        aggregate["global_align_e1_sq_sum"] += float(row.get("align_e1_sq_sum", 0.0))
        aggregate["global_align_e3_sq_sum"] += float(row.get("align_e3_sq_sum", 0.0))

        value = row.get("align_e1_sq_min")
        if value is not None and np.isfinite(float(value)):
            aggregate_value = aggregate["global_align_e1_sq_min"]
            if aggregate_value is None or float(value) < float(aggregate_value):
                aggregate["global_align_e1_sq_min"] = float(value)
        value = row.get("align_e3_sq_min")
        if value is not None and np.isfinite(float(value)):
            aggregate_value = aggregate["global_align_e3_sq_min"]
            if aggregate_value is None or float(value) < float(aggregate_value):
                aggregate["global_align_e3_sq_min"] = float(value)
        value = row.get("align_e1_sq_max")
        if value is not None and np.isfinite(float(value)):
            aggregate_value = aggregate["global_align_e1_sq_max"]
            if aggregate_value is None or float(value) > float(aggregate_value):
                aggregate["global_align_e1_sq_max"] = float(value)
        value = row.get("align_e3_sq_max")
        if value is not None and np.isfinite(float(value)):
            aggregate_value = aggregate["global_align_e3_sq_max"]
            if aggregate_value is None or float(value) > float(aggregate_value):
                aggregate["global_align_e3_sq_max"] = float(value)

    v = int(aggregate["global_finite_cell_count"])
    aggregate["global_lambda2_positive_fraction"] = _fraction(aggregate["global_lambda2_positive_count"], v)
    aggregate["global_lambda2_negative_fraction"] = _fraction(aggregate["global_lambda2_negative_count"], v)
    aggregate["global_lambda2_zero_fraction"] = _fraction(aggregate["global_lambda2_zero_count"], v)
    region_count = int(aggregate["global_alignment_region_cell_count"])
    aggregate["global_align_e1_fraction"] = _fraction(aggregate["global_align_e1_count"], region_count)
    aggregate["global_align_e3_fraction"] = _fraction(aggregate["global_align_e3_count"], region_count)
    aggregate["global_align_tie_fraction"] = _fraction(aggregate["global_align_tie_count"], region_count)
    aggregate["global_align_rule_success_fraction"] = _fraction(
        aggregate["global_align_rule_success_count"],
        region_count,
    )
    aggregate["global_align_rule_mismatch_fraction"] = _fraction(
        aggregate["global_align_rule_mismatch_count"],
        region_count,
    )
    aggregate["global_align_e1_sq_mean"] = (
        aggregate["global_align_e1_sq_sum"] / float(region_count) if region_count > 0 else 0.0
    )
    aggregate["global_align_e3_sq_mean"] = (
        aggregate["global_align_e3_sq_sum"] / float(region_count) if region_count > 0 else 0.0
    )
    return aggregate


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Raw N128 archive path")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Analyze a single frame index.")
    parser.add_argument("--frame-limit", type=_positive_int, default=None, help="Limit number of frames from start")
    parser.add_argument(
        "--zero-eps",
        type=float,
        default=DEFAULT_ZERO_EPS,
        help="Signed threshold for comparisons (e.g., lambda2 sign and alignment tie tolerance).",
    )
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
                "aggregate": {"processed_frames": 0, "ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 1},
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
    statuses: list[str] = []
    for slot in frame_indices:
        try:
            status, row = _evaluate_frame(
                slot=int(slot),
                snapshot=int(slot),
                raw_bundle=raw_bundle,
                eps=float(args.zero_eps),
                warnings=warnings,
            )
        except Exception as exc:
            status = ERROR_STATUS
            row = {
                "frame": int(slot),
                "snapshot_index": int(slot),
                "source": str(raw_bundle.path),
                "status": ERROR_STATUS,
                "errors": [f"frame_evaluation_error:{exc}"],
            }
        rows.append(row)
        statuses.append(str(status))

    aggregate = _build_aggregate(rows)
    if not rows:
        status = MISSING_REQUIRED_STATUS
    elif any(row_status == ERROR_STATUS for row_status in statuses):
        status = ERROR_STATUS
    elif any(row_status == MISSING_REQUIRED_STATUS for row_status in statuses):
        status = PARTIAL_STATUS
    elif any(row_status == PARTIAL_STATUS for row_status in statuses):
        status = PARTIAL_STATUS
    elif any(not _is_benign_warning(warning) for warning in warnings):
        status = PARTIAL_STATUS
    else:
        status = OK_STATUS
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
            "selected_frames": [int(i) for i in frame_indices],
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
