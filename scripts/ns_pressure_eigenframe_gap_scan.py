#!/usr/bin/env python3
"""Scan pressure-Hessian projections in the strain eigenframe on raw N128 archives.

For each selected snapshot this script reconstructs:
- the symmetric strain tensor from velocity gradients via spectral derivatives,
- the full pressure Hessian from pressure snapshots via spectral second derivatives,
and emits compressive-zone (`lambda2 >= 0`) telemetry for off-diagonal projections
`P12`, `P13`, and `P23` in the strain eigenframe e1/e2/e3 along with simple
threshold summaries by `delta1 = |lambda1|`.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_pressure_eigenframe_gap_scan.py"
CONTRACT = "ns_pressure_eigenframe_gap_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_PRESSURE_EIGENFRAME_GAP_SCAN"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {
    OK_STATUS,
    PARTIAL_STATUS,
    MISSING_REQUIRED_STATUS,
    ERROR_STATUS,
}

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_pressure_eigenframe_gap_scan_N128_20260621.json"
)
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_THRESHOLD_VALUES = (0.0, 0.05, 0.10, 0.20, 0.50, 1.0)
TOLERANCE = 1.0e-12

CONTROL_CARD = {
    "O": "Scan raw N128 flow with pressure Hessian eigenframe projections.",
    "R": (
        "Load raw velocity+pressure snapshots, reconstruct spectral strain and pressure "
        "Hessian, project P12/P13/P23 into the strain eigenframe, and bin by "
        "delta1=|lambda1| on the compressive zone lambda2>=0."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed: malformed fields, non-finite reconstruction, or arithmetic violations are explicit errors.",
    "L": "Emit per-frame and aggregate telemetry with threshold summaries and scaled off-diagonal pressure-Hessian proxies.",
    "P": ROUTE_DECISION,
    "G": "Empirical scan only; no theorem promotion or Clay claim.",
    "F": "Any malformed raw payload, shape/rank mismatch, non-finite arithmetic, or invariant failure marks failure.",
}

BENIGN_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "pressure_snapshots axis-1 singleton component axis detected",
    "pressure_snapshots trailing singleton component axis detected",
    "pressure last-axis singleton component axis detected",
    "domain_length unavailable; using fallback 6.283185307179586",
)


def _is_benign_warning(value: str) -> bool:
    if not isinstance(value, str):
        return False
    return any(value.endswith(suffix) or value == suffix for suffix in BENIGN_WARNING_SUFFIXES)


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be nonnegative")
    return parsed


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _parse_thresholds(value: list[float]) -> list[float]:
    parsed: list[float] = []
    seen: set[float] = set()
    for item in value:
        if not math.isfinite(item):
            continue
        threshold = float(item)
        if threshold < 0.0:
            continue
        if threshold in seen:
            continue
        seen.add(threshold)
        parsed.append(threshold)
    parsed.sort()
    return parsed


def _to_threshold_key(value: float) -> float:
    return float(f"{float(value):.12g}")


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


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
                for key in (
                    "domain_length",
                    "length",
                    "L",
                    "grid_length",
                    "dx",
                    "grid_spacing",
                    "dh",
                ):
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
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        try:
            return float(scalar), name
        except Exception:
            continue
    return None, None


def _infer_domain_length(data: dict[str, np.ndarray], n: int, warnings: list[str]) -> float:
    domain_length, domain_key = _read_scalar_metadata(data, ("domain_length", "length", "L", "grid_length"))
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
        elif not math.isclose(domain, spacing_value * n, rel_tol=1.0e-8, abs_tol=1.0e-8):
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
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots trailing channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        if velocity.ndim == 4 and velocity.shape[1] == 3:
            warnings.append("velocity_snapshots axis-1 channel layout detected")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 4 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots last-axis layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"unsupported velocity_snapshots shape {velocity.shape!r}")

    if all(key in data for key in ("u", "v", "w")):
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

    raise ValueError("no velocity components available")


def _select_pressure_field(data: dict[str, np.ndarray], warnings: list[str]) -> tuple[np.ndarray, str]:
    for key in ("pressure_snapshots", "pressure", "p", "pressure_hat"):
        if key not in data:
            continue
        pressure = np.asarray(data[key], dtype=np.float64)
        if pressure.ndim in (3, 4, 5):
            return pressure, key
    raise ValueError("no pressure field available")


def _normalize_velocity_shape(arr: np.ndarray, name: str) -> tuple[np.ndarray, bool, int]:
    if arr.ndim == 3:
        if arr.shape[0] != arr.shape[1] or arr.shape[1] != arr.shape[2]:
            raise ValueError(f"{name} must be cubic, got {arr.shape!r}")
        return arr, False, 1

    if arr.ndim == 4:
        if arr.shape[1] == arr.shape[2] == arr.shape[3]:
            frame_count = int(arr.shape[0])
            if frame_count == 1:
                return np.asarray(arr[0], dtype=np.float64), False, 1
            return np.asarray(arr, dtype=np.float64), True, frame_count
        raise ValueError(f"{name} unsupported 4D shape {arr.shape!r}")

    raise ValueError(f"{name} unsupported rank {arr.ndim}: {arr.shape!r}")


def _normalize_pressure_shape(
    pressure: np.ndarray,
    pressure_name: str,
    warnings: list[str],
) -> tuple[np.ndarray, bool, int]:
    if pressure.ndim == 3:
        if pressure.shape[0] != pressure.shape[1] or pressure.shape[1] != pressure.shape[2]:
            raise ValueError(f"{pressure_name} must be cubic, got {pressure.shape!r}")
        return pressure, False, 1

    if pressure.ndim == 4:
        if pressure.shape[1] == pressure.shape[2] == pressure.shape[3]:
            frame_count = int(pressure.shape[0])
            if frame_count == 1:
                return np.asarray(pressure[0], dtype=np.float64), False, 1
            return np.asarray(pressure, dtype=np.float64), True, frame_count

        if pressure.shape[-1] == 1 and pressure.shape[0] == pressure.shape[1] == pressure.shape[2]:
            warnings.append(f"{pressure_name} trailing singleton component axis detected")
            return np.asarray(pressure[..., 0], dtype=np.float64), False, 1

        if pressure.shape[1] == 1 and pressure.shape[2] == pressure.shape[3]:
            warnings.append(f"{pressure_name} axis-1 singleton component axis detected")
            frame_count = int(pressure.shape[0])
            if frame_count == 1:
                return np.asarray(pressure[0, 0], dtype=np.float64), False, 1
            return np.asarray(pressure[:, 0], dtype=np.float64), True, frame_count

        raise ValueError(f"unsupported pressure shape {pressure.shape!r}")

    if pressure.ndim == 5:
        if pressure.shape[1] == 1 and pressure.shape[2] == pressure.shape[3] == pressure.shape[4]:
            warnings.append(f"{pressure_name} axis-1 singleton component axis detected")
            frame_count = int(pressure.shape[0])
            if frame_count == 1:
                return np.asarray(pressure[0, 0], dtype=np.float64), False, 1
            return np.asarray(pressure[:, 0], dtype=np.float64), True, frame_count

        if pressure.shape[-1] == 1 and pressure.shape[0] == pressure.shape[2] == pressure.shape[3] == pressure.shape[4]:
            warnings.append(f"{pressure_name} trailing singleton component axis detected")
            frame_count = int(pressure.shape[0])
            if frame_count == 1:
                return np.asarray(pressure[0, ..., 0], dtype=np.float64), False, 1
            return np.asarray(pressure[..., 0], dtype=np.float64), True, frame_count

        if pressure.shape[-1] == 1 and pressure.shape[0] == pressure.shape[1] == pressure.shape[2] == pressure.shape[3]:
            warnings.append("pressure last-axis singleton component axis detected")
            return np.asarray(pressure[..., 0], dtype=np.float64), False, 1

        raise ValueError(f"unsupported pressure shape {pressure.shape!r}")

    raise ValueError(f"unsupported pressure rank {pressure.ndim}: {pressure.shape!r}")


@dataclass(frozen=True)
class RawBundle:
    path: Path
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    pressure: np.ndarray
    velocity_has_frame_axis: bool
    pressure_has_frame_axis: bool
    velocity_frame_count: int
    pressure_frame_count: int
    frame_count: int
    domain_length: float


def _load_raw_bundle(path: Path, warnings: list[str]) -> RawBundle:
    data = _load_npz(path)

    u_raw, v_raw, w_raw = _select_velocity_components(data, warnings)
    u, velocity_has_frame_axis, velocity_frame_count = _normalize_velocity_shape(u_raw, "u")
    v, _, vfc = _normalize_velocity_shape(v_raw, "v")
    w, _, wfc = _normalize_velocity_shape(w_raw, "w")
    if vfc != velocity_frame_count or wfc != velocity_frame_count:
        raise ValueError("velocity components have mismatched frame counts")

    pressure_raw, pressure_name = _select_pressure_field(data, warnings)
    pressure, pressure_has_frame_axis, pressure_frame_count = _normalize_pressure_shape(
        pressure_raw,
        pressure_name,
        warnings,
    )

    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError("velocity component shapes differ")

    n = int(u.shape[0])
    if velocity_has_frame_axis:
        n = int(u.shape[1])
        if u.shape[1] != u.shape[2] or u.shape[2] != u.shape[3]:
            raise ValueError(f"velocity snapshot shape not cubic: {u.shape!r}")
    else:
        if u.shape[0] != u.shape[1] or u.shape[1] != u.shape[2]:
            raise ValueError(f"velocity snapshot shape not cubic: {u.shape!r}")

    if pressure_has_frame_axis:
        if pressure.shape[1] != n or pressure.shape[2] != n or pressure.shape[3] != n:
            raise ValueError(f"pressure frame shape does not match velocity grid: {pressure.shape!r}")
    else:
        if pressure.shape[0] != n or pressure.shape[1] != n or pressure.shape[2] != n:
            raise ValueError(f"pressure shape does not match velocity grid: {pressure.shape!r}")

    if not np.all(np.isfinite(u)) or not np.all(np.isfinite(v)) or not np.all(np.isfinite(w)):
        raise ValueError(f"raw velocity contains non-finite values in {path}")
    if not np.all(np.isfinite(pressure)):
        raise ValueError(f"raw pressure contains non-finite values in {path}")

    domain_length = _infer_domain_length(data, n, warnings)

    frame_count = max(velocity_frame_count, pressure_frame_count)
    if velocity_frame_count > 1 and pressure_frame_count == 1:
        warnings.append("pressure snapshots have single frame; broadcast across velocity frames")
    if pressure_frame_count > 1 and velocity_frame_count == 1:
        warnings.append("velocity snapshots have single frame; broadcast across pressure frames")

    return RawBundle(
        path=path,
        u=u,
        v=v,
        w=w,
        pressure=pressure,
        velocity_has_frame_axis=velocity_has_frame_axis,
        pressure_has_frame_axis=pressure_has_frame_axis,
        velocity_frame_count=velocity_frame_count,
        pressure_frame_count=pressure_frame_count,
        frame_count=frame_count,
        domain_length=domain_length,
    )


def _frame_velocity(bundle: RawBundle, snapshot: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if bundle.velocity_has_frame_axis:
        if snapshot < 0:
            raise ValueError("snapshot index must be nonnegative")
        if snapshot >= int(bundle.velocity_frame_count):
            raise ValueError(f"velocity has only {bundle.velocity_frame_count} frames")
        return (
            np.asarray(bundle.u[snapshot], dtype=np.float64),
            np.asarray(bundle.v[snapshot], dtype=np.float64),
            np.asarray(bundle.w[snapshot], dtype=np.float64),
        )

    if snapshot < 0:
        raise ValueError("snapshot index must be nonnegative")
    return (
        np.asarray(bundle.u, dtype=np.float64),
        np.asarray(bundle.v, dtype=np.float64),
        np.asarray(bundle.w, dtype=np.float64),
    )


def _frame_pressure(bundle: RawBundle, snapshot: int) -> np.ndarray:
    if bundle.pressure_has_frame_axis:
        if snapshot < 0:
            raise ValueError("snapshot index must be nonnegative")
        if snapshot >= int(bundle.pressure_frame_count):
            raise ValueError(f"pressure has only {bundle.pressure_frame_count} frames")
        return np.asarray(bundle.pressure[snapshot], dtype=np.float64)

    if snapshot < 0:
        raise ValueError("snapshot index must be nonnegative")
    return np.asarray(bundle.pressure, dtype=np.float64)


def _spectral_derivative(field: np.ndarray, axis: int, kx: np.ndarray, ky: np.ndarray, kz: np.ndarray) -> np.ndarray:
    transformed = np.fft.fftn(field, axes=(0, 1, 2))
    if axis == 0:
        return np.fft.ifftn(1j * kx * transformed, axes=(0, 1, 2)).real
    if axis == 1:
        return np.fft.ifftn(1j * ky * transformed, axes=(0, 1, 2)).real
    if axis == 2:
        return np.fft.ifftn(1j * kz * transformed, axes=(0, 1, 2)).real
    raise ValueError(f"axis must be 0,1,2; got {axis}")


def _spectral_hessian(field: np.ndarray, domain_length: float) -> np.ndarray:
    if not isinstance(field, np.ndarray):
        raise ValueError("pressure field must be an ndarray")
    if field.ndim != 3:
        raise ValueError(f"pressure field must be 3D, got {field.shape!r}")
    n = int(field.shape[0])
    if field.shape[1] != n or field.shape[2] != n:
        raise ValueError(f"pressure field must be cubic, got {field.shape!r}")
    if n <= 1:
        raise ValueError(f"pressure grid size must be > 1, got {n}")
    if not math.isfinite(float(domain_length)) or float(domain_length) <= 0.0:
        raise ValueError("domain_length must be finite positive")

    spacing = float(domain_length) / float(n)
    k = 2.0 * math.pi * np.fft.fftfreq(n, d=spacing)
    kx = k.reshape(n, 1, 1)
    ky = k.reshape(1, n, 1)
    kz = k.reshape(1, 1, n)

    pressure_hat = np.fft.fftn(field, axes=(0, 1, 2))
    hessian = np.empty((3, 3) + field.shape, dtype=np.float64)
    hessian[0, 0] = np.fft.ifftn(-(kx * kx) * pressure_hat, axes=(0, 1, 2)).real
    hessian[1, 1] = np.fft.ifftn(-(ky * ky) * pressure_hat, axes=(0, 1, 2)).real
    hessian[2, 2] = np.fft.ifftn(-(kz * kz) * pressure_hat, axes=(0, 1, 2)).real
    hessian[0, 1] = np.fft.ifftn(-(kx * ky) * pressure_hat, axes=(0, 1, 2)).real
    hessian[1, 0] = hessian[0, 1]
    hessian[0, 2] = np.fft.ifftn(-(kx * kz) * pressure_hat, axes=(0, 1, 2)).real
    hessian[2, 0] = hessian[0, 2]
    hessian[1, 2] = np.fft.ifftn(-(ky * kz) * pressure_hat, axes=(0, 1, 2)).real
    hessian[2, 1] = hessian[1, 2]
    return hessian


def _strain_and_eigen_projections(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    pressure_hessian: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, float]:
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError("velocity component shapes differ")
    if u.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {u.shape!r}")
    n = int(u.shape[0])
    if u.shape[1] != n or u.shape[2] != n:
        raise ValueError(f"velocity fields must be cubic, got {u.shape!r}")
    if n <= 1:
        raise ValueError("velocity grid size must be > 1")
    if pressure_hessian.shape != (3, 3, n, n, n):
        raise ValueError(f"pressure_hessian shape mismatch: {pressure_hessian.shape!r}")
    if not math.isfinite(float(domain_length)) or float(domain_length) <= 0.0:
        raise ValueError("domain_length must be finite positive")

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

    strain = np.empty((n, n, n, 3, 3), dtype=np.float64)
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
    e1 = np.asarray(eigenvectors[..., 0], dtype=np.float64)
    e2 = np.asarray(eigenvectors[..., 1], dtype=np.float64)
    e3 = np.asarray(eigenvectors[..., 2], dtype=np.float64)

    h_tensor = np.moveaxis(pressure_hessian, (0, 1), (-2, -1))
    # Off-diagonal projections in eigenframe: P_ij = e_i^T H e_j
    projected = np.einsum("...ia,...ij,...jb->...ab", eigenvectors, h_tensor, eigenvectors)
    p12 = np.asarray(projected[..., 0, 1], dtype=np.float64)
    p13 = np.asarray(projected[..., 0, 2], dtype=np.float64)
    p23 = np.asarray(projected[..., 1, 2], dtype=np.float64)

    pressure_hessian_norm = float(np.sqrt(np.mean(np.sum(h_tensor * h_tensor, axis=(-2, -1)))))
    return lambda1, lambda2, e1, e2, e3, p12, p13, p23, pressure_hessian_norm


def _sum_stats(values: np.ndarray) -> tuple[float, float, float, float]:
    if values.size == 0:
        return 0.0, 0.0, 0.0, 0.0
    values_f = np.asarray(values, dtype=np.float64)
    return float(np.sum(values_f)), float(np.min(values_f)), float(np.max(values_f)), float(np.mean(values_f))


def _empty_gap_row(threshold: float) -> dict[str, Any]:
    return {
        "delta1_threshold": float(threshold),
        "cell_count": 0,
        "p12_abs_sum": 0.0,
        "p12_abs_min": None,
        "p12_abs_max": None,
        "p12_abs_mean": 0.0,
        "p13_abs_sum": 0.0,
        "p13_abs_min": None,
        "p13_abs_max": None,
        "p13_abs_mean": 0.0,
        "p23_abs_sum": 0.0,
        "p23_abs_min": None,
        "p23_abs_max": None,
        "p23_abs_mean": 0.0,
        "p12_scaled_sum": 0.0,
        "p12_scaled_min": None,
        "p12_scaled_max": None,
        "p12_scaled_mean": 0.0,
        "p12_scaled_ge_one_count": 0,
        "p12_scaled_ge_one_fraction": 0.0,
        "p13_scaled_sum": 0.0,
        "p13_scaled_min": None,
        "p13_scaled_max": None,
        "p13_scaled_mean": 0.0,
        "p13_scaled_ge_one_count": 0,
        "p13_scaled_ge_one_fraction": 0.0,
        "p23_scaled_sum": 0.0,
        "p23_scaled_min": None,
        "p23_scaled_max": None,
        "p23_scaled_mean": 0.0,
        "p23_scaled_ge_one_count": 0,
        "p23_scaled_ge_one_fraction": 0.0,
        "zone_fraction": 0.0,
    }


def _gap_row(
    threshold: float,
    delta1: np.ndarray,
    p12_abs: np.ndarray,
    p13_abs: np.ndarray,
    p23_abs: np.ndarray,
    p12_scaled: np.ndarray,
    p13_scaled: np.ndarray,
    p23_scaled: np.ndarray,
    compressive_count: int,
) -> dict[str, Any]:
    if delta1.size == 0:
        return _empty_gap_row(float(threshold))

    mask = delta1 >= float(threshold)
    cell_count = int(np.count_nonzero(mask))
    if cell_count == 0:
        return _empty_gap_row(float(threshold))

    p12 = np.asarray(p12_abs[mask], dtype=np.float64)
    p13 = np.asarray(p13_abs[mask], dtype=np.float64)
    p23 = np.asarray(p23_abs[mask], dtype=np.float64)
    s12 = np.asarray(p12_scaled[mask], dtype=np.float64)
    s13 = np.asarray(p13_scaled[mask], dtype=np.float64)
    s23 = np.asarray(p23_scaled[mask], dtype=np.float64)

    p12_abs_sum, p12_abs_min, p12_abs_max, p12_abs_mean = _sum_stats(p12)
    p13_abs_sum, p13_abs_min, p13_abs_max, p13_abs_mean = _sum_stats(p13)
    p23_abs_sum, p23_abs_min, p23_abs_max, p23_abs_mean = _sum_stats(p23)

    p12_scaled_sum, p12_scaled_min, p12_scaled_max, p12_scaled_mean = _sum_stats(s12)
    p13_scaled_sum, p13_scaled_min, p13_scaled_max, p13_scaled_mean = _sum_stats(s13)
    p23_scaled_sum, p23_scaled_min, p23_scaled_max, p23_scaled_mean = _sum_stats(s23)

    row: dict[str, Any] = {
        "delta1_threshold": float(threshold),
        "cell_count": int(cell_count),
        "p12_abs_sum": p12_abs_sum,
        "p12_abs_min": p12_abs_min,
        "p12_abs_max": p12_abs_max,
        "p12_abs_mean": p12_abs_mean,
        "p13_abs_sum": p13_abs_sum,
        "p13_abs_min": p13_abs_min,
        "p13_abs_max": p13_abs_max,
        "p13_abs_mean": p13_abs_mean,
        "p23_abs_sum": p23_abs_sum,
        "p23_abs_min": p23_abs_min,
        "p23_abs_max": p23_abs_max,
        "p23_abs_mean": p23_abs_mean,
        "p12_scaled_sum": p12_scaled_sum,
        "p12_scaled_min": p12_scaled_min,
        "p12_scaled_max": p12_scaled_max,
        "p12_scaled_mean": p12_scaled_mean,
        "p12_scaled_ge_one_count": int(np.count_nonzero(s12 >= 1.0)),
        "p12_scaled_ge_one_fraction": _fraction(int(np.count_nonzero(s12 >= 1.0)), cell_count),
        "p13_scaled_sum": p13_scaled_sum,
        "p13_scaled_min": p13_scaled_min,
        "p13_scaled_max": p13_scaled_max,
        "p13_scaled_mean": p13_scaled_mean,
        "p13_scaled_ge_one_count": int(np.count_nonzero(s13 >= 1.0)),
        "p13_scaled_ge_one_fraction": _fraction(int(np.count_nonzero(s13 >= 1.0)), cell_count),
        "p23_scaled_sum": p23_scaled_sum,
        "p23_scaled_min": p23_scaled_min,
        "p23_scaled_max": p23_scaled_max,
        "p23_scaled_mean": p23_scaled_mean,
        "p23_scaled_ge_one_count": int(np.count_nonzero(s23 >= 1.0)),
        "p23_scaled_ge_one_fraction": _fraction(int(np.count_nonzero(s23 >= 1.0)), cell_count),
        "zone_fraction": _fraction(cell_count, compressive_count),
    }
    return row


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
        "raw_archive": str(bundle.path),
        "velocity_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
        "pressure_source": f"raw:{bundle.path.name}#snapshot={snapshot}",
        "pressure_hessian_source": "spectral_pressure_hessian",
    }

    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        p = _frame_pressure(bundle, snapshot)
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"snapshot_selection_error: {exc}"]
        row["pressure_hessian_source"] = None
        return ERROR_STATUS, row

    if u.ndim != 3 or v.ndim != 3 or w.ndim != 3:
        row["status"] = ERROR_STATUS
        row["errors"] = ["snapshot must be 3D velocity fields"]
        return ERROR_STATUS, row
    if p.ndim != 3:
        row["status"] = ERROR_STATUS
        row["errors"] = ["snapshot pressure must be 3D"]
        return ERROR_STATUS, row

    if not np.all(np.isfinite(u)) or not np.all(np.isfinite(v)) or not np.all(np.isfinite(w)) or not np.all(np.isfinite(p)):
        row["status"] = ERROR_STATUS
        row["errors"] = ["non-finite raw snapshot values"]
        return ERROR_STATUS, row

    try:
        pressure_hessian = _spectral_hessian(p, bundle.domain_length)
        lambda1, lambda2, e1, e2, e3, p12, p13, p23, pressure_hessian_norm = _strain_and_eigen_projections(
            u,
            v,
            w,
            pressure_hessian,
            bundle.domain_length,
        )
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"reconstruction_failed: {exc}"]
        return ERROR_STATUS, row

    if lambda1.shape != lambda2.shape or p12.shape != lambda1.shape or p13.shape != lambda1.shape or p23.shape != lambda1.shape:
        row["status"] = ERROR_STATUS
        row["errors"] = ["reconstruction produced inconsistent field shapes"]
        return ERROR_STATUS, row

    finite = (
        np.isfinite(lambda1)
        & np.isfinite(lambda2)
        & np.isfinite(e1).all(axis=(-1, -2))
        & np.isfinite(e2).all(axis=(-1, -2))
        & np.isfinite(e3).all(axis=(-1, -2))
        & np.isfinite(p12)
        & np.isfinite(p13)
        & np.isfinite(p23)
    )
    cell_count = int(lambda2.size)
    finite_count = int(np.count_nonzero(finite))
    row["cell_count"] = cell_count
    row["finite_cell_count"] = finite_count
    if finite_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["no finite reconstructed cells"]
        return ERROR_STATUS, row

    if finite_count != cell_count:
        row["finite_cell_count"] = finite_count
        warnings.append(f"frame {slot}: excluded {cell_count - finite_count} non-finite reconstructed cells")

    lambda1_f = np.asarray(lambda1[finite], dtype=np.float64)
    lambda2_f = np.asarray(lambda2[finite], dtype=np.float64)

    l2_pos = int(np.count_nonzero(lambda2_f > eps))
    l2_neg = int(np.count_nonzero(lambda2_f < -eps))
    l2_zero = int(lambda2_f.size - l2_pos - l2_neg)
    row.update(
        {
            "lambda2_positive_count": l2_pos,
            "lambda2_negative_count": l2_neg,
            "lambda2_zero_count": l2_zero,
            "lambda2_positive_fraction": _fraction(l2_pos, finite_count),
            "lambda2_negative_fraction": _fraction(l2_neg, finite_count),
            "lambda2_zero_fraction": _fraction(l2_zero, finite_count),
        }
    )

    compressive_mask = finite & (lambda2 >= 0.0)
    compressive_count = int(np.count_nonzero(compressive_mask))
    row["compressive_zone_cell_count"] = compressive_count

    if compressive_count == 0:
        row["status"] = MISSING_REQUIRED_STATUS
        row["errors"] = ["no finite compressive cells (lambda2 >= 0)"]
        row.update(
            {
                "delta1_sum": 0.0,
                "delta1_min": None,
                "delta1_max": None,
                "delta1_mean": 0.0,
                "p12_abs_sum": 0.0,
                "p12_abs_min": None,
                "p12_abs_max": None,
                "p12_abs_mean": 0.0,
                "p13_abs_sum": 0.0,
                "p13_abs_min": None,
                "p13_abs_max": None,
                "p13_abs_mean": 0.0,
                "p23_abs_sum": 0.0,
                "p23_abs_min": None,
                "p23_abs_max": None,
                "p23_abs_mean": 0.0,
                "p12_scaled_sum": 0.0,
                "p12_scaled_min": None,
                "p12_scaled_max": None,
                "p12_scaled_mean": 0.0,
                "p12_scaled_ge_one_count": 0,
                "p12_scaled_ge_one_fraction": 0.0,
                "p13_scaled_sum": 0.0,
                "p13_scaled_min": None,
                "p13_scaled_max": None,
                "p13_scaled_mean": 0.0,
                "p13_scaled_ge_one_count": 0,
                "p13_scaled_ge_one_fraction": 0.0,
                "p23_scaled_sum": 0.0,
                "p23_scaled_min": None,
                "p23_scaled_max": None,
                "p23_scaled_mean": 0.0,
                "p23_scaled_ge_one_count": 0,
                "p23_scaled_ge_one_fraction": 0.0,
                "pressure_hessian_norm": pressure_hessian_norm,
                "pressure_hessian_frobenius_norm": pressure_hessian_norm,
                "gap_threshold_rows": [_empty_gap_row(threshold) for threshold in thresholds],
            }
        )
        return MISSING_REQUIRED_STATUS, row

    delta1 = np.abs(lambda1[compressive_mask])
    p12_abs = np.abs(p12[compressive_mask])
    p13_abs = np.abs(p13[compressive_mask])
    p23_abs = np.abs(p23[compressive_mask])

    scale = np.maximum(delta1, eps)
    p12_scaled = p12_abs / scale
    p13_scaled = p13_abs / scale
    p23_scaled = p23_abs / scale

    delta1_sum, delta1_min, delta1_max, delta1_mean = _sum_stats(delta1)
    p12_abs_sum, p12_abs_min, p12_abs_max, p12_abs_mean = _sum_stats(p12_abs)
    p13_abs_sum, p13_abs_min, p13_abs_max, p13_abs_mean = _sum_stats(p13_abs)
    p23_abs_sum, p23_abs_min, p23_abs_max, p23_abs_mean = _sum_stats(p23_abs)
    p12_scaled_sum, p12_scaled_min, p12_scaled_max, p12_scaled_mean = _sum_stats(p12_scaled)
    p13_scaled_sum, p13_scaled_min, p13_scaled_max, p13_scaled_mean = _sum_stats(p13_scaled)
    p23_scaled_sum, p23_scaled_min, p23_scaled_max, p23_scaled_mean = _sum_stats(p23_scaled)

    p12_scaled_ge_one_count = int(np.count_nonzero(p12_scaled >= 1.0))
    p13_scaled_ge_one_count = int(np.count_nonzero(p13_scaled >= 1.0))
    p23_scaled_ge_one_count = int(np.count_nonzero(p23_scaled >= 1.0))

    row.update(
        {
            "pressure_hessian_norm": pressure_hessian_norm,
            "pressure_hessian_frobenius_norm": pressure_hessian_norm,
            "delta1_sum": delta1_sum,
            "delta1_min": delta1_min,
            "delta1_max": delta1_max,
            "delta1_mean": delta1_mean,
            "p12_abs_sum": p12_abs_sum,
            "p12_abs_min": p12_abs_min,
            "p12_abs_max": p12_abs_max,
            "p12_abs_mean": p12_abs_mean,
            "p13_abs_sum": p13_abs_sum,
            "p13_abs_min": p13_abs_min,
            "p13_abs_max": p13_abs_max,
            "p13_abs_mean": p13_abs_mean,
            "p23_abs_sum": p23_abs_sum,
            "p23_abs_min": p23_abs_min,
            "p23_abs_max": p23_abs_max,
            "p23_abs_mean": p23_abs_mean,
            "p12_scaled_sum": p12_scaled_sum,
            "p12_scaled_min": p12_scaled_min,
            "p12_scaled_max": p12_scaled_max,
            "p12_scaled_mean": p12_scaled_mean,
            "p12_scaled_ge_one_count": p12_scaled_ge_one_count,
            "p12_scaled_ge_one_fraction": _fraction(p12_scaled_ge_one_count, compressive_count),
            "p13_scaled_sum": p13_scaled_sum,
            "p13_scaled_min": p13_scaled_min,
            "p13_scaled_max": p13_scaled_max,
            "p13_scaled_mean": p13_scaled_mean,
            "p13_scaled_ge_one_count": p13_scaled_ge_one_count,
            "p13_scaled_ge_one_fraction": _fraction(p13_scaled_ge_one_count, compressive_count),
            "p23_scaled_sum": p23_scaled_sum,
            "p23_scaled_min": p23_scaled_min,
            "p23_scaled_max": p23_scaled_max,
            "p23_scaled_mean": p23_scaled_mean,
            "p23_scaled_ge_one_count": p23_scaled_ge_one_count,
            "p23_scaled_ge_one_fraction": _fraction(p23_scaled_ge_one_count, compressive_count),
        }
    )

    gap_rows: list[dict[str, Any]] = []
    for threshold in thresholds:
        gap_rows.append(
            _gap_row(
                threshold=threshold,
                delta1=delta1,
                p12_abs=p12_abs,
                p13_abs=p13_abs,
                p23_abs=p23_abs,
                p12_scaled=p12_scaled,
                p13_scaled=p13_scaled,
                p23_scaled=p23_scaled,
                compressive_count=compressive_count,
            )
        )

    row["gap_threshold_rows"] = gap_rows
    row["status"] = OK_STATUS if finite_count == cell_count else PARTIAL_STATUS
    return row["status"], row


def _accumulate_threshold_min_max(bucket: dict[str, Any], candidate_key: str, value: Any) -> None:
    if not isinstance(value, (int, float)) or not math.isfinite(float(value)):
        return
    candidate = float(value)
    if bucket.get(candidate_key) is None:
        bucket[candidate_key] = candidate
        return
    current = float(bucket[candidate_key])
    if candidate_key.endswith("_min"):
        if candidate < current:
            bucket[candidate_key] = candidate
    else:
        if candidate > current:
            bucket[candidate_key] = candidate


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
        "global_delta1_sum": 0.0,
        "global_delta1_min": None,
        "global_delta1_max": None,
        "global_delta1_mean": 0.0,
        "global_p12_abs_sum": 0.0,
        "global_p12_abs_min": None,
        "global_p12_abs_max": None,
        "global_p12_abs_mean": 0.0,
        "global_p13_abs_sum": 0.0,
        "global_p13_abs_min": None,
        "global_p13_abs_max": None,
        "global_p13_abs_mean": 0.0,
        "global_p23_abs_sum": 0.0,
        "global_p23_abs_min": None,
        "global_p23_abs_max": None,
        "global_p23_abs_mean": 0.0,
        "global_p12_scaled_sum": 0.0,
        "global_p12_scaled_min": None,
        "global_p12_scaled_max": None,
        "global_p12_scaled_mean": 0.0,
        "global_p12_scaled_ge_one_count": 0,
        "global_p12_scaled_ge_one_fraction": 0.0,
        "global_p13_scaled_sum": 0.0,
        "global_p13_scaled_min": None,
        "global_p13_scaled_max": None,
        "global_p13_scaled_mean": 0.0,
        "global_p13_scaled_ge_one_count": 0,
        "global_p13_scaled_ge_one_fraction": 0.0,
        "global_p23_scaled_sum": 0.0,
        "global_p23_scaled_min": None,
        "global_p23_scaled_max": None,
        "global_p23_scaled_mean": 0.0,
        "global_p23_scaled_ge_one_count": 0,
        "global_p23_scaled_ge_one_fraction": 0.0,
    }

    normalized_thresholds = [
        float(_to_threshold_key(float(value))) for value in thresholds
    ]
    gap_threshold_rows: dict[float, dict[str, Any]] = {
        float(threshold): _empty_gap_row(float(threshold)) for threshold in normalized_thresholds
    }

    for row in rows:
        status = row.get("status")
        if status == OK_STATUS:
            aggregate["ok_frames"] += 1
        elif status == PARTIAL_STATUS:
            aggregate["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            aggregate["missing_frames"] += 1
        else:
            aggregate["error_frames"] += 1

        aggregate["global_cell_count"] += int(row.get("cell_count", 0))
        aggregate["global_finite_cell_count"] += int(row.get("finite_cell_count", 0))

        aggregate["global_lambda2_positive_count"] += int(row.get("lambda2_positive_count", 0))
        aggregate["global_lambda2_negative_count"] += int(row.get("lambda2_negative_count", 0))
        aggregate["global_lambda2_zero_count"] += int(row.get("lambda2_zero_count", 0))
        aggregate["global_compressive_zone_cell_count"] += int(row.get("compressive_zone_cell_count", 0))

        aggregate["global_delta1_sum"] += float(row.get("delta1_sum", 0.0))
        aggregate["global_p12_abs_sum"] += float(row.get("p12_abs_sum", 0.0))
        aggregate["global_p13_abs_sum"] += float(row.get("p13_abs_sum", 0.0))
        aggregate["global_p23_abs_sum"] += float(row.get("p23_abs_sum", 0.0))
        aggregate["global_p12_scaled_sum"] += float(row.get("p12_scaled_sum", 0.0))
        aggregate["global_p13_scaled_sum"] += float(row.get("p13_scaled_sum", 0.0))
        aggregate["global_p23_scaled_sum"] += float(row.get("p23_scaled_sum", 0.0))

        aggregate["global_p12_scaled_ge_one_count"] += int(row.get("p12_scaled_ge_one_count", 0))
        aggregate["global_p13_scaled_ge_one_count"] += int(row.get("p13_scaled_ge_one_count", 0))
        aggregate["global_p23_scaled_ge_one_count"] += int(row.get("p23_scaled_ge_one_count", 0))

        _accumulate_threshold_min_max(aggregate, "global_delta1_min", row.get("delta1_min"))
        _accumulate_threshold_min_max(aggregate, "global_delta1_max", row.get("delta1_max"))
        for aggregate_key, row_key in (
            ("global_p12_abs_min", "p12_abs_min"),
            ("global_p13_abs_min", "p13_abs_min"),
            ("global_p23_abs_min", "p23_abs_min"),
            ("global_p12_abs_max", "p12_abs_max"),
            ("global_p13_abs_max", "p13_abs_max"),
            ("global_p23_abs_max", "p23_abs_max"),
            ("global_p12_scaled_min", "p12_scaled_min"),
            ("global_p13_scaled_min", "p13_scaled_min"),
            ("global_p23_scaled_min", "p23_scaled_min"),
            ("global_p12_scaled_max", "p12_scaled_max"),
            ("global_p13_scaled_max", "p13_scaled_max"),
            ("global_p23_scaled_max", "p23_scaled_max"),
        ):
            _accumulate_threshold_min_max(aggregate, aggregate_key, row.get(row_key))

        threshold_rows = row.get("gap_threshold_rows")
        if not isinstance(threshold_rows, list):
            continue
        for entry in threshold_rows:
            if not isinstance(entry, dict):
                continue
            try:
                threshold = float(_to_threshold_key(float(entry.get("delta1_threshold"))))
            except (TypeError, ValueError):
                continue
            if not math.isfinite(threshold) or threshold < 0.0:
                continue

            bucket = gap_threshold_rows.setdefault(threshold, _empty_gap_row(threshold))
            bucket["cell_count"] += int(entry.get("cell_count", 0))
            for proxy_key in ("p12_abs_sum", "p13_abs_sum", "p23_abs_sum"):
                bucket[proxy_key] += float(entry.get(proxy_key, 0.0))
            for proxy_key in ("p12_scaled_sum", "p13_scaled_sum", "p23_scaled_sum"):
                bucket[proxy_key] += float(entry.get(proxy_key, 0.0))
            for proxy_key in (
                "p12_scaled_ge_one_count",
                "p13_scaled_ge_one_count",
                "p23_scaled_ge_one_count",
            ):
                bucket[proxy_key] += int(entry.get(proxy_key, 0))

            for proxy_key in (
                "p12_abs_min",
                "p12_abs_max",
                "p13_abs_min",
                "p13_abs_max",
                "p23_abs_min",
                "p23_abs_max",
                "p12_scaled_min",
                "p12_scaled_max",
                "p13_scaled_min",
                "p13_scaled_max",
                "p23_scaled_min",
                "p23_scaled_max",
            ):
                _accumulate_threshold_min_max(bucket, proxy_key, entry.get(proxy_key))

    compressive_total = int(aggregate["global_compressive_zone_cell_count"])
    aggregate["global_delta1_mean"] = _fraction(aggregate["global_delta1_sum"], compressive_total)
    aggregate["global_p12_abs_mean"] = _fraction(aggregate["global_p12_abs_sum"], compressive_total)
    aggregate["global_p13_abs_mean"] = _fraction(aggregate["global_p13_abs_sum"], compressive_total)
    aggregate["global_p23_abs_mean"] = _fraction(aggregate["global_p23_abs_sum"], compressive_total)
    aggregate["global_p12_scaled_mean"] = _fraction(aggregate["global_p12_scaled_sum"], compressive_total)
    aggregate["global_p13_scaled_mean"] = _fraction(aggregate["global_p13_scaled_sum"], compressive_total)
    aggregate["global_p23_scaled_mean"] = _fraction(aggregate["global_p23_scaled_sum"], compressive_total)

    aggregate["global_lambda2_positive_fraction"] = _fraction(int(aggregate["global_lambda2_positive_count"]), int(aggregate["global_finite_cell_count"]))
    aggregate["global_lambda2_negative_fraction"] = _fraction(int(aggregate["global_lambda2_negative_count"]), int(aggregate["global_finite_cell_count"]))
    aggregate["global_lambda2_zero_fraction"] = _fraction(int(aggregate["global_lambda2_zero_count"]), int(aggregate["global_finite_cell_count"]))

    aggregate["global_compressive_zone_fraction"] = _fraction(compressive_total, int(aggregate["global_finite_cell_count"]))
    aggregate["global_p12_scaled_ge_one_fraction"] = _fraction(int(aggregate["global_p12_scaled_ge_one_count"]), compressive_total)
    aggregate["global_p13_scaled_ge_one_fraction"] = _fraction(int(aggregate["global_p13_scaled_ge_one_count"]), compressive_total)
    aggregate["global_p23_scaled_ge_one_fraction"] = _fraction(int(aggregate["global_p23_scaled_ge_one_count"]), compressive_total)

    aggregate_gap_rows = []
    for threshold in sorted(gap_threshold_rows.keys()):
        bucket = gap_threshold_rows[threshold]
        cell_count = int(bucket.get("cell_count", 0))
        if cell_count > 0:
            bucket["p12_abs_mean"] = _fraction(bucket.get("p12_abs_sum", 0.0), cell_count)
            bucket["p13_abs_mean"] = _fraction(bucket.get("p13_abs_sum", 0.0), cell_count)
            bucket["p23_abs_mean"] = _fraction(bucket.get("p23_abs_sum", 0.0), cell_count)
            bucket["p12_scaled_mean"] = _fraction(bucket.get("p12_scaled_sum", 0.0), cell_count)
            bucket["p13_scaled_mean"] = _fraction(bucket.get("p13_scaled_sum", 0.0), cell_count)
            bucket["p23_scaled_mean"] = _fraction(bucket.get("p23_scaled_sum", 0.0), cell_count)
            bucket["p12_scaled_ge_one_fraction"] = _fraction(int(bucket.get("p12_scaled_ge_one_count", 0)), cell_count)
            bucket["p13_scaled_ge_one_fraction"] = _fraction(int(bucket.get("p13_scaled_ge_one_count", 0)), cell_count)
            bucket["p23_scaled_ge_one_fraction"] = _fraction(int(bucket.get("p23_scaled_ge_one_count", 0)), cell_count)
        else:
            bucket["p12_abs_mean"] = 0.0
            bucket["p13_abs_mean"] = 0.0
            bucket["p23_abs_mean"] = 0.0
            bucket["p12_scaled_mean"] = 0.0
            bucket["p13_scaled_mean"] = 0.0
            bucket["p23_scaled_mean"] = 0.0
            bucket["p12_scaled_ge_one_fraction"] = 0.0
            bucket["p13_scaled_ge_one_fraction"] = 0.0
            bucket["p23_scaled_ge_one_fraction"] = 0.0
        bucket["zone_fraction"] = _fraction(cell_count, compressive_total)
        aggregate_gap_rows.append(bucket)

    aggregate["gap_threshold_rows"] = aggregate_gap_rows
    aggregate["scaled_ge_one_threshold_curve"] = [
        {
            "delta1_threshold": row["delta1_threshold"],
            "p12_scaled_ge_one_fraction": row["p12_scaled_ge_one_fraction"],
            "p13_scaled_ge_one_fraction": row["p13_scaled_ge_one_fraction"],
            "p23_scaled_ge_one_fraction": row["p23_scaled_ge_one_fraction"],
            "zone_fraction": row["zone_fraction"],
        }
        for row in aggregate_gap_rows
    ]
    return aggregate


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Raw archive containing velocity+pressure snapshots")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Single frame index to process")
    parser.add_argument("--frame-limit", type=_positive_int, default=None, help="Maximum frame count to process")
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS, help="Scale-floor epsilon for delta-normalization")
    parser.add_argument(
        "--delta1-thresholds",
        type=float,
        nargs="+",
        default=list(DEFAULT_THRESHOLD_VALUES),
        help="Delta1 thresholds for gap summaries",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def _build_error_payload(path: Path, errors: list[str], warnings: list[str], args: argparse.Namespace) -> dict[str, Any]:
    return {
        "contract": CONTRACT,
        "status": ERROR_STATUS,
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
            "delta1_thresholds": [],
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
        "errors": errors,
        "changed_files": [str(path)],
    }


def main() -> int:
    args = _parse_args()

    if args.zero_eps < 0.0:
        raise ValueError("--zero-eps must be nonnegative")

    thresholds = _parse_thresholds(list(args.delta1_thresholds))
    warnings: list[str] = []

    if not args.raw_archive.exists():
        payload = _build_error_payload(args.output, [f"raw_archive_missing: {args.raw_archive}"], warnings, args)
        payload["inputs"]["delta1_thresholds"] = thresholds
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    if not thresholds:
        payload = _build_error_payload(
            args.output,
            ["delta1-thresholds parse to empty set"],
            warnings,
            args,
        )
        payload["inputs"]["delta1_thresholds"] = []
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    try:
        bundle = _load_raw_bundle(args.raw_archive, warnings)
    except Exception as exc:
        payload = _build_error_payload(
            args.output,
            [f"raw_load_failure: {exc}"],
            warnings,
            args,
        )
        payload["inputs"]["delta1_thresholds"] = thresholds
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    frame_indices = list(range(int(bundle.frame_count)))
    if args.frame is not None:
        if args.frame >= int(bundle.frame_count):
            payload = _build_error_payload(
                args.output,
                [f"requested frame {args.frame} out of range for {bundle.frame_count} frames"],
                warnings,
                args,
            )
            payload["inputs"]["delta1_thresholds"] = thresholds
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
            print(_json_text(payload, args.pretty))
            return 1
        frame_indices = [int(args.frame)]
    if args.frame_limit is not None:
        frame_indices = frame_indices[: int(args.frame_limit)]

    rows: list[dict[str, Any]] = []
    row_statuses: list[str] = []
    for slot in frame_indices:
        status, row = _evaluate_frame(
            slot=int(slot),
            snapshot=int(slot),
            bundle=bundle,
            eps=float(args.zero_eps),
            thresholds=thresholds,
            warnings=warnings,
        )
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
        "errors": [],
        "changed_files": [str(args.output)],
    }
    if status in {ERROR_STATUS, MISSING_REQUIRED_STATUS}:
        payload["errors"] = ["scan completed with non-ok status"]

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
