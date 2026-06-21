#!/usr/bin/env python3
"""Scan Pi-c decomposition telemetry on raw N128 velocity snapshots."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_compressive_pi_decomposition_scan.py"
CONTRACT = "ns_compressive_pi_decomposition_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_COMPRESSIVE_PI_DECOMPOSITION_SCAN"

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
    "ns_compressive_pi_decomposition_scan_N128_20260621.json"
)
DEFAULT_ZERO_EPS = 1.0e-12


CONTROL_CARD = {
    "O": "Build fail-closed Pi-c decomposition telemetry on the raw N128 velocity archive.",
    "R": (
        "Reconstruct strain and vorticity from raw velocity frames; project vorticity into "
        "the strain eigenframe; emit per-frame and aggregate telemetry for Pi-c terms "
        "lambda_i * omega_i^2 on the compressive zone lambda2 >= 0."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed: malformed reconstruction or arithmetic failures become explicit error/missing rows.",
    "L": "Load raw archive, reconstruct derivatives via FFT, compute eigenframes and per-cell Pi components.",
    "P": ROUTE_DECISION,
    "G": "Empirical scan only; no theorem/clay claim is made by this script.",
    "F": "Any status downgrade is explicit; only schema-complete outputs are considered promotable candidates.",
}


LEGACY_AXIS_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "velocity axis-1 channel layout detected",
    "velocity trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback",
)


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


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


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


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    if not path.exists():
        raise FileNotFoundError(f"raw archive missing: {path}")
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in payload:
        try:
            metadata = json.loads(str(np.asarray(payload["meta_json"]).item()))
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
        domain_value = _coerce_float(domain_length, name=domain_key or "domain_length")
        if domain_value <= 0.0:
            raise ValueError("domain_length must be positive")
    else:
        domain_value = None

    spacing, spacing_key = _read_scalar_metadata(data, ("grid_spacing", "dx", "dh"))
    if spacing is not None:
        spacing_value = _coerce_float(spacing, name=spacing_key or "grid_spacing")
        if spacing_value <= 0.0:
            raise ValueError("grid_spacing must be positive")
        if domain_value is None:
            domain_value = float(spacing_value * n)
        elif not math.isclose(domain_value, spacing_value * n, rel_tol=1e-8, abs_tol=1e-8):
            warnings.append(
                f"domain_length/grid_spacing mismatch: {domain_value} vs {spacing_value * n} (using domain_length)"
            )
    if domain_value is not None:
        return domain_value

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

    if {"u", "v", "w"}.issubset(data):
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


def _sign_counts(values: np.ndarray, eps: float) -> tuple[int, int, int]:
    pos = int(np.count_nonzero(values > eps))
    neg = int(np.count_nonzero(values < -eps))
    zero = int(values.size - pos - neg)
    return pos, neg, zero


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
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
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
        raise ValueError("domain_length must be finite and positive")

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
    omega_sq = omega_x * omega_x + omega_y * omega_y + omega_z * omega_z

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    lambda1 = np.asarray(eigenvalues[..., 0], dtype=np.float64)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    lambda3 = np.asarray(eigenvalues[..., 2], dtype=np.float64)
    e1 = np.asarray(eigenvectors[..., :, 0], dtype=np.float64)
    e2 = np.asarray(eigenvectors[..., :, 1], dtype=np.float64)
    e3 = np.asarray(eigenvectors[..., :, 2], dtype=np.float64)
    return (
        lambda1,
        lambda2,
        lambda3,
        e1,
        e2,
        e3,
        omega_x,
        omega_y,
        omega_z,
        omega_sq,
    )


def _empty_pi_row() -> dict[str, Any]:
    return {
        "cell_count": 0,
        "finite_cell_count": 0,
        "lambda1_positive_count": 0,
        "lambda1_negative_count": 0,
        "lambda1_zero_count": 0,
        "lambda1_positive_fraction": 0.0,
        "lambda1_negative_fraction": 0.0,
        "lambda1_zero_fraction": 0.0,
        "lambda2_positive_count": 0,
        "lambda2_negative_count": 0,
        "lambda2_zero_count": 0,
        "lambda2_positive_fraction": 0.0,
        "lambda2_negative_fraction": 0.0,
        "lambda2_zero_fraction": 0.0,
        "lambda3_positive_count": 0,
        "lambda3_negative_count": 0,
        "lambda3_zero_count": 0,
        "lambda3_positive_fraction": 0.0,
        "lambda3_negative_fraction": 0.0,
        "lambda3_zero_fraction": 0.0,
        "compressive_zone_cell_count": 0,
        "compressive_zone_omega_nonzero_count": 0,
        "compressive_zone_omega_nonzero_fraction": 0.0,
        "compressive_zone_omega_sq_sum": 0.0,
        "compressive_dominates_count": 0,
        "extensional_dominates_count": 0,
        "dominance_tie_count": 0,
        "compressive_dominates_fraction": 0.0,
        "extensional_dominates_fraction": 0.0,
        "dominance_tie_fraction": 0.0,
        "dominance_gap_sum": 0.0,
        "dominance_gap_mean": 0.0,
        "dominance_gap_min": None,
        "dominance_gap_max": None,
        "pi1_positive_count": 0,
        "pi1_negative_count": 0,
        "pi1_zero_count": 0,
        "pi1_positive_fraction": 0.0,
        "pi1_negative_fraction": 0.0,
        "pi1_zero_fraction": 0.0,
        "pi2_positive_count": 0,
        "pi2_negative_count": 0,
        "pi2_zero_count": 0,
        "pi2_positive_fraction": 0.0,
        "pi2_negative_fraction": 0.0,
        "pi2_zero_fraction": 0.0,
        "pi3_positive_count": 0,
        "pi3_negative_count": 0,
        "pi3_zero_count": 0,
        "pi3_positive_fraction": 0.0,
        "pi3_negative_fraction": 0.0,
        "pi3_zero_fraction": 0.0,
        "pi1_sum": 0.0,
        "pi2_sum": 0.0,
        "pi3_sum": 0.0,
        "pi_sum": 0.0,
        "pi_sum_abs": 0.0,
        "pi1_min": 0.0,
        "pi1_max": 0.0,
        "pi1_mean": 0.0,
        "pi2_min": 0.0,
        "pi2_max": 0.0,
        "pi2_mean": 0.0,
        "pi3_min": 0.0,
        "pi3_max": 0.0,
        "pi3_mean": 0.0,
        "pi1_abs_sum": 0.0,
        "pi2_abs_sum": 0.0,
        "pi3_abs_sum": 0.0,
        "omega1_sum": 0.0,
        "omega2_sum": 0.0,
        "omega3_sum": 0.0,
        "omega1_sq_sum": 0.0,
        "omega2_sq_sum": 0.0,
        "omega3_sq_sum": 0.0,
        "omega1_sq_mean": 0.0,
        "omega2_sq_mean": 0.0,
        "omega3_sq_mean": 0.0,
        "pi_compression_gap_sum": 0.0,
        "pi_compression_gap_mean": 0.0,
        "pi_compression_gap_min": None,
        "pi_compression_gap_max": None,
    }


def _evaluate_frame(slot: int, snapshot: int, raw_bundle: RawBundle, eps: float, warnings: list[str]) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(raw_bundle.path),
        "lambda2_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
        "vorticity_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
        "eigenframe_source": f"raw:{raw_bundle.path.name}#snapshot={snapshot}",
    }

    u, v, w = _raw_velocity_frame(raw_bundle, snapshot)
    (
        lambda1,
        lambda2,
        lambda3,
        e1,
        e2,
        e3,
        omega_x,
        omega_y,
        omega_z,
        omega_sq,
    ) = _strain_eigen_and_vorticity_from_velocity(
        u,
        v,
        w,
        raw_bundle.domain_length,
    )

    if lambda1.shape != lambda2.shape or lambda3.shape != lambda2.shape:
        raise ValueError("reconstructed scalar field shapes diverged")
    if e1.shape[:3] != lambda2.shape or e2.shape[:3] != lambda2.shape or e3.shape[:3] != lambda2.shape:
        raise ValueError("reconstructed eigenframe shapes diverged")
    if omega_x.shape != lambda2.shape or omega_sq.shape != lambda2.shape:
        raise ValueError("reconstructed vorticity shapes diverged")

    finite = (
        np.isfinite(lambda1)
        & np.isfinite(lambda2)
        & np.isfinite(lambda3)
        & np.isfinite(e1).all(axis=-1)
        & np.isfinite(e2).all(axis=-1)
        & np.isfinite(e3).all(axis=-1)
        & np.isfinite(omega_x)
        & np.isfinite(omega_y)
        & np.isfinite(omega_z)
        & np.isfinite(omega_sq)
    )

    cell_count = int(lambda2.size)
    finite_count = int(np.count_nonzero(finite))
    row["cell_count"] = cell_count
    row["finite_cell_count"] = finite_count
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite reconstructed fields"]
        return ERROR_STATUS, row
    if finite_count < cell_count:
        warnings.append(f"frame {slot}: excluded {cell_count - finite_count} non-finite reconstructed cells")

    lambda1_f = np.asarray(lambda1[finite], dtype=np.float64)
    lambda2_f = np.asarray(lambda2[finite], dtype=np.float64)
    lambda3_f = np.asarray(lambda3[finite], dtype=np.float64)
    l1_pos, l1_neg, l1_zero = _sign_counts(lambda1_f, eps)
    l2_pos, l2_neg, l2_zero = _sign_counts(lambda2_f, eps)
    l3_pos, l3_neg, l3_zero = _sign_counts(lambda3_f, eps)

    row["lambda1_positive_count"] = l1_pos
    row["lambda1_negative_count"] = l1_neg
    row["lambda1_zero_count"] = l1_zero
    row["lambda2_positive_count"] = l2_pos
    row["lambda2_negative_count"] = l2_neg
    row["lambda2_zero_count"] = l2_zero
    row["lambda3_positive_count"] = l3_pos
    row["lambda3_negative_count"] = l3_neg
    row["lambda3_zero_count"] = l3_zero
    row["lambda1_positive_fraction"] = _fraction(l1_pos, finite_count)
    row["lambda1_negative_fraction"] = _fraction(l1_neg, finite_count)
    row["lambda1_zero_fraction"] = _fraction(l1_zero, finite_count)
    row["lambda2_positive_fraction"] = _fraction(l2_pos, finite_count)
    row["lambda2_negative_fraction"] = _fraction(l2_neg, finite_count)
    row["lambda2_zero_fraction"] = _fraction(l2_zero, finite_count)
    row["lambda3_positive_fraction"] = _fraction(l3_pos, finite_count)
    row["lambda3_negative_fraction"] = _fraction(l3_neg, finite_count)
    row["lambda3_zero_fraction"] = _fraction(l3_zero, finite_count)

    compressive_mask = finite & (lambda2 >= 0.0)
    compressive_count = int(np.count_nonzero(compressive_mask))
    row["compressive_zone_cell_count"] = compressive_count
    if compressive_count == 0:
        row.update(_empty_pi_row())
        row["status"] = MISSING_REQUIRED_STATUS
        row["errors"] = ["no finite lambda2>=0 cells for Pi decomposition telemetry"]
        return MISSING_REQUIRED_STATUS, row

    compressive_omega_sq = omega_sq[compressive_mask]
    omega_nonzero_mask = compressive_omega_sq > eps
    omega_nonzero_count = int(np.count_nonzero(omega_nonzero_mask))
    row["compressive_zone_omega_nonzero_count"] = omega_nonzero_count
    row["compressive_zone_omega_nonzero_fraction"] = _fraction(omega_nonzero_count, compressive_count)
    row["compressive_zone_omega_sq_sum"] = float(np.sum(compressive_omega_sq))

    # Project vorticity onto local eigenframe.
    e1_c = np.asarray(e1[compressive_mask], dtype=np.float64)
    e2_c = np.asarray(e2[compressive_mask], dtype=np.float64)
    e3_c = np.asarray(e3[compressive_mask], dtype=np.float64)
    omx = np.asarray(omega_x[compressive_mask], dtype=np.float64)
    omy = np.asarray(omega_y[compressive_mask], dtype=np.float64)
    omz = np.asarray(omega_z[compressive_mask], dtype=np.float64)

    omega1 = omx * e1_c[:, 0] + omy * e1_c[:, 1] + omz * e1_c[:, 2]
    omega2 = omx * e2_c[:, 0] + omy * e2_c[:, 1] + omz * e2_c[:, 2]
    omega3 = omx * e3_c[:, 0] + omy * e3_c[:, 1] + omz * e3_c[:, 2]
    row["omega1_sum"] = float(np.sum(omega1))
    row["omega2_sum"] = float(np.sum(omega2))
    row["omega3_sum"] = float(np.sum(omega3))
    omega1_sq = omega1 * omega1
    omega2_sq = omega2 * omega2
    omega3_sq = omega3 * omega3
    row["omega1_sq_sum"] = float(np.sum(omega1_sq))
    row["omega2_sq_sum"] = float(np.sum(omega2_sq))
    row["omega3_sq_sum"] = float(np.sum(omega3_sq))
    row["omega1_sq_mean"] = float(np.mean(omega1_sq))
    row["omega2_sq_mean"] = float(np.mean(omega2_sq))
    row["omega3_sq_mean"] = float(np.mean(omega3_sq))

    lambda1_c = np.asarray(lambda1[compressive_mask], dtype=np.float64)
    lambda2_c = np.asarray(lambda2[compressive_mask], dtype=np.float64)
    lambda3_c = np.asarray(lambda3[compressive_mask], dtype=np.float64)

    pi1 = lambda1_c * omega1_sq
    pi2 = lambda2_c * omega2_sq
    pi3 = lambda3_c * omega3_sq

    if not np.all(np.isfinite(pi1)) or not np.all(np.isfinite(pi2)) or not np.all(np.isfinite(pi3)):
        row["status"] = ERROR_STATUS
        row["errors"] = ["pi terms contain non-finite values"]
        return ERROR_STATUS, row

    pi1_pos, pi1_neg, pi1_zero = _sign_counts(pi1, eps)
    pi2_pos, pi2_neg, pi2_zero = _sign_counts(pi2, eps)
    pi3_pos, pi3_neg, pi3_zero = _sign_counts(pi3, eps)
    row["pi1_positive_count"] = pi1_pos
    row["pi1_negative_count"] = pi1_neg
    row["pi1_zero_count"] = pi1_zero
    row["pi2_positive_count"] = pi2_pos
    row["pi2_negative_count"] = pi2_neg
    row["pi2_zero_count"] = pi2_zero
    row["pi3_positive_count"] = pi3_pos
    row["pi3_negative_count"] = pi3_neg
    row["pi3_zero_count"] = pi3_zero
    row["pi1_positive_fraction"] = _fraction(pi1_pos, compressive_count)
    row["pi1_negative_fraction"] = _fraction(pi1_neg, compressive_count)
    row["pi1_zero_fraction"] = _fraction(pi1_zero, compressive_count)
    row["pi2_positive_fraction"] = _fraction(pi2_pos, compressive_count)
    row["pi2_negative_fraction"] = _fraction(pi2_neg, compressive_count)
    row["pi2_zero_fraction"] = _fraction(pi2_zero, compressive_count)
    row["pi3_positive_fraction"] = _fraction(pi3_pos, compressive_count)
    row["pi3_negative_fraction"] = _fraction(pi3_neg, compressive_count)
    row["pi3_zero_fraction"] = _fraction(pi3_zero, compressive_count)

    row["pi1_sum"] = float(np.sum(pi1))
    row["pi2_sum"] = float(np.sum(pi2))
    row["pi3_sum"] = float(np.sum(pi3))
    pi_sum = row["pi1_sum"] + row["pi2_sum"] + row["pi3_sum"]
    row["pi_sum"] = pi_sum
    row["pi_sum_abs"] = float(np.sum(np.abs(pi1) + np.abs(pi2) + np.abs(pi3)))
    row["pi1_min"] = float(np.min(pi1))
    row["pi1_max"] = float(np.max(pi1))
    row["pi1_mean"] = float(np.mean(pi1))
    row["pi2_min"] = float(np.min(pi2))
    row["pi2_max"] = float(np.max(pi2))
    row["pi2_mean"] = float(np.mean(pi2))
    row["pi3_min"] = float(np.min(pi3))
    row["pi3_max"] = float(np.max(pi3))
    row["pi3_mean"] = float(np.mean(pi3))
    row["pi1_abs_sum"] = float(np.sum(np.abs(pi1)))
    row["pi2_abs_sum"] = float(np.sum(np.abs(pi2)))
    row["pi3_abs_sum"] = float(np.sum(np.abs(pi3)))

    # Compressive/extensional dominance in compression frame:
    # compressive contribution magnitude is -min(pi1, 0);
    # extensional contribution is max(pi2,0) + max(pi3,0).
    compressive_mag = np.maximum(-pi1, 0.0)
    extensional_mag = np.maximum(pi2, 0.0) + np.maximum(pi3, 0.0)
    compressive_gap = compressive_mag - extensional_mag
    dominates_mask = compressive_gap > eps
    extensional_mask = compressive_gap < -eps
    tie_mask = ~(dominates_mask | extensional_mask)

    dominates_count = int(np.count_nonzero(dominates_mask))
    extensional_count = int(np.count_nonzero(extensional_mask))
    tie_count = int(np.count_nonzero(tie_mask))
    row["compressive_dominates_count"] = dominates_count
    row["extensional_dominates_count"] = extensional_count
    row["dominance_tie_count"] = tie_count
    row["compressive_dominates_fraction"] = _fraction(dominates_count, compressive_count)
    row["extensional_dominates_fraction"] = _fraction(extensional_count, compressive_count)
    row["dominance_tie_fraction"] = _fraction(tie_count, compressive_count)
    row["dominance_gap_sum"] = float(np.sum(compressive_gap))
    row["dominance_gap_mean"] = float(np.mean(compressive_gap))
    row["dominance_gap_min"] = float(np.min(compressive_gap))
    row["dominance_gap_max"] = float(np.max(compressive_gap))

    compression_only = np.maximum(-pi1, 0.0)
    row["pi_compression_gap_sum"] = float(np.sum(compression_only))
    row["pi_compression_gap_mean"] = float(np.mean(compression_only))
    row["pi_compression_gap_min"] = float(np.min(compression_only))
    row["pi_compression_gap_max"] = float(np.max(compression_only))

    status = OK_STATUS
    if finite_count < cell_count:
        status = PARTIAL_STATUS
    row["status"] = status
    return status, row


def _build_aggregate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate: dict[str, Any] = {
        "processed_frames": int(len(rows)),
        "ok_frames": 0,
        "partial_frames": 0,
        "missing_frames": 0,
        "error_frames": 0,
        "global_cell_count": 0,
        "global_finite_cell_count": 0,
        "global_lambda1_positive_count": 0,
        "global_lambda1_negative_count": 0,
        "global_lambda1_zero_count": 0,
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_lambda3_positive_count": 0,
        "global_lambda3_negative_count": 0,
        "global_lambda3_zero_count": 0,
        "global_compressive_zone_cell_count": 0,
        "global_compressive_zone_omega_nonzero_count": 0,
        "global_compressive_dominates_count": 0,
        "global_extensional_dominates_count": 0,
        "global_dominance_tie_count": 0,
        "global_pi1_positive_count": 0,
        "global_pi1_negative_count": 0,
        "global_pi1_zero_count": 0,
        "global_pi2_positive_count": 0,
        "global_pi2_negative_count": 0,
        "global_pi2_zero_count": 0,
        "global_pi3_positive_count": 0,
        "global_pi3_negative_count": 0,
        "global_pi3_zero_count": 0,
        "global_pi1_sum": 0.0,
        "global_pi2_sum": 0.0,
        "global_pi3_sum": 0.0,
        "global_pi_sum": 0.0,
        "global_pi_sum_abs": 0.0,
        "global_pi1_abs_sum": 0.0,
        "global_pi2_abs_sum": 0.0,
        "global_pi3_abs_sum": 0.0,
        "global_omega1_sq_sum": 0.0,
        "global_omega2_sq_sum": 0.0,
        "global_omega3_sq_sum": 0.0,
        "global_dominance_gap_sum": 0.0,
        "global_dominance_gap_min": None,
        "global_dominance_gap_max": None,
        "global_pi_compression_gap_sum": 0.0,
        "global_pi_compression_gap_min": None,
        "global_pi_compression_gap_max": None,
        "global_compressive_zone_omega_sq_sum": 0.0,
        "global_dominance_tie_count": 0,
        "global_pi1_min": None,
        "global_pi1_max": None,
        "global_pi2_min": None,
        "global_pi2_max": None,
        "global_pi3_min": None,
        "global_pi3_max": None,
        "global_omega1_sq_mean": 0.0,
        "global_omega2_sq_mean": 0.0,
        "global_omega3_sq_mean": 0.0,
        "global_dominance_fraction_check_sum": 0,
        "global_pi_count_sum": 0,
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
        aggregate["global_compressive_zone_cell_count"] += int(row.get("compressive_zone_cell_count", 0))
        aggregate["global_compressive_zone_omega_nonzero_count"] += int(
            row.get("compressive_zone_omega_nonzero_count", 0)
        )
        aggregate["global_compressive_dominates_count"] += int(row.get("compressive_dominates_count", 0))
        aggregate["global_extensional_dominates_count"] += int(row.get("extensional_dominates_count", 0))
        aggregate["global_dominance_tie_count"] += int(row.get("dominance_tie_count", 0))
        aggregate["global_dominance_fraction_check_sum"] += int(row.get("compressive_dominates_count", 0)) + int(
            row.get("extensional_dominates_count", 0)
        ) + int(row.get("dominance_tie_count", 0))

        for row_key, agg_key in (
            ("lambda1_positive_count", "global_lambda1_positive_count"),
            ("lambda1_negative_count", "global_lambda1_negative_count"),
            ("lambda1_zero_count", "global_lambda1_zero_count"),
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("lambda3_positive_count", "global_lambda3_positive_count"),
            ("lambda3_negative_count", "global_lambda3_negative_count"),
            ("lambda3_zero_count", "global_lambda3_zero_count"),
            ("pi1_positive_count", "global_pi1_positive_count"),
            ("pi1_negative_count", "global_pi1_negative_count"),
            ("pi1_zero_count", "global_pi1_zero_count"),
            ("pi2_positive_count", "global_pi2_positive_count"),
            ("pi2_negative_count", "global_pi2_negative_count"),
            ("pi2_zero_count", "global_pi2_zero_count"),
            ("pi3_positive_count", "global_pi3_positive_count"),
            ("pi3_negative_count", "global_pi3_negative_count"),
            ("pi3_zero_count", "global_pi3_zero_count"),
        ):
            aggregate[agg_key] += int(row.get(row_key, 0))
            aggregate["global_pi_count_sum"] += int(row.get(row_key, 0))

        aggregate["global_omega1_sq_sum"] += float(row.get("omega1_sq_sum", 0.0))
        aggregate["global_omega2_sq_sum"] += float(row.get("omega2_sq_sum", 0.0))
        aggregate["global_omega3_sq_sum"] += float(row.get("omega3_sq_sum", 0.0))
        aggregate["global_pi1_sum"] += float(row.get("pi1_sum", 0.0))
        aggregate["global_pi2_sum"] += float(row.get("pi2_sum", 0.0))
        aggregate["global_pi3_sum"] += float(row.get("pi3_sum", 0.0))
        aggregate["global_pi_sum"] += float(row.get("pi_sum", 0.0))
        aggregate["global_pi_sum_abs"] += float(row.get("pi_sum_abs", 0.0))
        aggregate["global_pi1_abs_sum"] += float(row.get("pi1_abs_sum", 0.0))
        aggregate["global_pi2_abs_sum"] += float(row.get("pi2_abs_sum", 0.0))
        aggregate["global_pi3_abs_sum"] += float(row.get("pi3_abs_sum", 0.0))
        aggregate["global_dominance_gap_sum"] += float(row.get("dominance_gap_sum", 0.0))
        aggregate["global_pi_compression_gap_sum"] += float(row.get("pi_compression_gap_sum", 0.0))
        aggregate["global_compressive_zone_omega_sq_sum"] += float(row.get("compressive_zone_omega_sq_sum", 0.0))

        value = row.get("dominance_gap_min")
        if value is not None:
            if aggregate["global_dominance_gap_min"] is None or float(value) < float(aggregate["global_dominance_gap_min"]):
                aggregate["global_dominance_gap_min"] = float(value)
        value = row.get("dominance_gap_max")
        if value is not None:
            if aggregate["global_dominance_gap_max"] is None or float(value) > float(aggregate["global_dominance_gap_max"]):
                aggregate["global_dominance_gap_max"] = float(value)
        value = row.get("pi_compression_gap_min")
        if value is not None:
            if (
                aggregate["global_pi_compression_gap_min"] is None
                or float(value) < float(aggregate["global_pi_compression_gap_min"])
            ):
                aggregate["global_pi_compression_gap_min"] = float(value)
        value = row.get("pi_compression_gap_max")
        if value is not None:
            if (
                aggregate["global_pi_compression_gap_max"] is None
                or float(value) > float(aggregate["global_pi_compression_gap_max"])
            ):
                aggregate["global_pi_compression_gap_max"] = float(value)

        for row_key, agg_key in (
            ("pi1_min", "global_pi1_min"),
            ("pi1_max", "global_pi1_max"),
            ("pi2_min", "global_pi2_min"),
            ("pi2_max", "global_pi2_max"),
            ("pi3_min", "global_pi3_min"),
            ("pi3_max", "global_pi3_max"),
        ):
            value = row.get(row_key)
            if value is None:
                continue
            current = aggregate[agg_key]
            if current is None or float(value) < float(current) and "min" in row_key:
                aggregate[agg_key] = float(value)
            if current is None or float(value) > float(current) and "max" in row_key:
                aggregate[agg_key] = float(value)

    finite = int(aggregate["global_finite_cell_count"])
    aggregate["global_lambda1_positive_fraction"] = _fraction(int(aggregate["global_lambda1_positive_count"]), finite)
    aggregate["global_lambda1_negative_fraction"] = _fraction(int(aggregate["global_lambda1_negative_count"]), finite)
    aggregate["global_lambda1_zero_fraction"] = _fraction(int(aggregate["global_lambda1_zero_count"]), finite)
    aggregate["global_lambda2_positive_fraction"] = _fraction(int(aggregate["global_lambda2_positive_count"]), finite)
    aggregate["global_lambda2_negative_fraction"] = _fraction(int(aggregate["global_lambda2_negative_count"]), finite)
    aggregate["global_lambda2_zero_fraction"] = _fraction(int(aggregate["global_lambda2_zero_count"]), finite)
    aggregate["global_lambda3_positive_fraction"] = _fraction(int(aggregate["global_lambda3_positive_count"]), finite)
    aggregate["global_lambda3_negative_fraction"] = _fraction(int(aggregate["global_lambda3_negative_count"]), finite)
    aggregate["global_lambda3_zero_fraction"] = _fraction(int(aggregate["global_lambda3_zero_count"]), finite)

    zone = int(aggregate["global_compressive_zone_cell_count"])
    aggregate["global_compressive_dominates_fraction"] = _fraction(
        int(aggregate["global_compressive_dominates_count"]),
        zone,
    )
    aggregate["global_extensional_dominates_fraction"] = _fraction(
        int(aggregate["global_extensional_dominates_count"]),
        zone,
    )
    aggregate["global_dominance_tie_fraction"] = _fraction(int(aggregate["global_dominance_tie_count"]), zone)
    aggregate["global_compressive_zone_omega_nonzero_fraction"] = _fraction(
        int(aggregate["global_compressive_zone_omega_nonzero_count"]),
        zone,
    )
    aggregate["global_pi1_positive_fraction"] = _fraction(int(aggregate["global_pi1_positive_count"]), zone)
    aggregate["global_pi1_negative_fraction"] = _fraction(int(aggregate["global_pi1_negative_count"]), zone)
    aggregate["global_pi1_zero_fraction"] = _fraction(int(aggregate["global_pi1_zero_count"]), zone)
    aggregate["global_pi2_positive_fraction"] = _fraction(int(aggregate["global_pi2_positive_count"]), zone)
    aggregate["global_pi2_negative_fraction"] = _fraction(int(aggregate["global_pi2_negative_count"]), zone)
    aggregate["global_pi2_zero_fraction"] = _fraction(int(aggregate["global_pi2_zero_count"]), zone)
    aggregate["global_pi3_positive_fraction"] = _fraction(int(aggregate["global_pi3_positive_count"]), zone)
    aggregate["global_pi3_negative_fraction"] = _fraction(int(aggregate["global_pi3_negative_count"]), zone)
    aggregate["global_pi3_zero_fraction"] = _fraction(int(aggregate["global_pi3_zero_count"]), zone)

    aggregate["global_pi1_omega1_mean"] = (
        aggregate["global_pi1_sum"] / float(aggregate["global_compressive_zone_cell_count"])
        if zone > 0
        else 0.0
    )
    aggregate["global_pi2_omega2_mean"] = (
        aggregate["global_pi2_sum"] / float(aggregate["global_compressive_zone_cell_count"])
        if zone > 0
        else 0.0
    )
    aggregate["global_pi3_omega3_mean"] = (
        aggregate["global_pi3_sum"] / float(aggregate["global_compressive_zone_cell_count"])
        if zone > 0
        else 0.0
    )
    aggregate["global_pi_sum_from_parts"] = (
        aggregate["global_pi1_sum"] + aggregate["global_pi2_sum"] + aggregate["global_pi3_sum"]
    )

    aggregate["global_omega1_sq_mean"] = (
        aggregate["global_omega1_sq_sum"] / float(aggregate["global_compressive_zone_cell_count"]) if zone > 0 else 0.0
    )
    aggregate["global_omega2_sq_mean"] = (
        aggregate["global_omega2_sq_sum"] / float(aggregate["global_compressive_zone_cell_count"]) if zone > 0 else 0.0
    )
    aggregate["global_omega3_sq_mean"] = (
        aggregate["global_omega3_sq_sum"] / float(aggregate["global_compressive_zone_cell_count"]) if zone > 0 else 0.0
    )
    return aggregate


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Raw N128 archive path")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Single frame index to analyze")
    parser.add_argument("--frame-limit", type=_positive_int, default=None, help="Limit number of frames to analyze")
    parser.add_argument(
        "--zero-eps",
        type=float,
        default=DEFAULT_ZERO_EPS,
        help="Signed tolerance for sign/fraction comparisons",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output scan JSON path.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    if args.zero_eps < 0.0:
        raise ValueError("--zero-eps must be nonnegative")

    warnings: list[str] = []
    try:
        bundle = _load_raw_bundle(args.raw_archive, warnings)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        output_payload = {
            "contract": CONTRACT,
            **{"O": CONTROL_CARD["O"], "R": CONTROL_CARD["R"], "C": CONTROL_CARD["C"], "S": CONTROL_CARD["S"], "L": CONTROL_CARD["L"], "P": CONTROL_CARD["P"], "G": CONTROL_CARD["G"], "F": CONTROL_CARD["F"]},
            "control_card": CONTROL_CARD,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "authority": _authority(),
            "input": {
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "zero_eps": float(args.zero_eps),
                "selected_frames": None,
            },
            "frames": [],
            "aggregate": {
                "processed_frames": 0,
                "ok_frames": 0,
                "partial_frames": 0,
                "missing_frames": 0,
                "error_frames": 0,
            },
            "warnings": warnings,
            "errors": [str(exc)],
            "changed_files": [str(args.raw_archive)],
        }
        output = _json_text(output_payload, args.pretty) + "\n"
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
        print(output, end="")
        return 1

    if args.frame is not None:
        selected_frames = [args.frame]
    elif args.frame_limit is not None:
        if args.frame_limit <= 0:
            selected_frames = []
        else:
            selected_frames = list(range(min(int(args.frame_limit), int(bundle.frame_count))))
    else:
        selected_frames = list(range(int(bundle.frame_count)))

    rows: list[dict[str, Any]] = []
    for slot, snapshot in enumerate(selected_frames):
        try:
            status, row = _evaluate_frame(slot, snapshot, bundle, args.zero_eps, warnings)
        except Exception as exc:
            status = ERROR_STATUS
            row = {
                "frame": int(slot),
                "snapshot_index": int(snapshot),
                "status": status,
                "source": str(bundle.path),
                "lambda2_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
                "vorticity_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
                "eigenframe_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
                "cell_count": 0,
                "finite_cell_count": 0,
                "errors": [f"{type(exc).__name__}: {exc}"],
            }
        row["frame"] = int(slot)
        row["snapshot_index"] = int(snapshot)
        rows.append(row)

        if status in (PARTIAL_STATUS, ERROR_STATUS):
            warnings.append(f"frame {slot}: {status}")

    aggregate = _build_aggregate(rows)

    overall_status = OK_STATUS
    for row in rows:
        status = row.get("status")
        if status == ERROR_STATUS:
            overall_status = ERROR_STATUS
            break
        if status == MISSING_REQUIRED_STATUS:
            if overall_status != ERROR_STATUS:
                overall_status = PARTIAL_STATUS
        elif status == PARTIAL_STATUS and overall_status == OK_STATUS:
            overall_status = PARTIAL_STATUS

    output_payload = {
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "status": overall_status,
        "authority": _authority(),
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "input": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "selected_frames": selected_frames,
            "raw_bundle_frame_count": int(bundle.frame_count),
        },
        "frames": rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": [],
        "changed_files": [str(args.output), str(args.raw_archive)],
    }

    if rows and all(row.get("status") == ERROR_STATUS for row in rows):
        output_payload["status"] = ERROR_STATUS
    if overall_status != ERROR_STATUS and any(row.get("status") == MISSING_REQUIRED_STATUS for row in rows):
        output_payload["status"] = PARTIAL_STATUS

    args.output.parent.mkdir(parents=True, exist_ok=True)
    output_text = _json_text(output_payload, args.pretty) + "\n"
    args.output.write_text(output_text, encoding="utf-8")
    print(output_text, end="")
    return 1 if output_payload["status"] == ERROR_STATUS else 0


if __name__ == "__main__":
    raise SystemExit(main())
