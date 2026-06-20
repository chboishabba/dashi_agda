#!/usr/bin/env python3
"""Compute Betchov identity targets on raw N128 velocity snapshots.

For each processed frame, emit:
* integral det(S)
* integral Pi = ω_i S_ij ω_j
* residual = integral det(S) + integral Pi / 4

Inputs are empirical.  Missing fields and reconstruction failures are surfaced via
explicit partial/missing/error statuses.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_betchov_identity_scan.py"
CONTRACT = "ns_betchov_identity_scan"
ROUTE_DECISION = "FAIL_CLOSED_BETCHOV_IDENTITY_SCAN"

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
    "ns_betchov_identity_scan_N128_20260620.json"
)
DEFAULT_ZERO_EPS = 1.0e-12
CHECK_TOLERANCE = 1.0e-11
DEFAULT_EPS = 1.0e-15


CONTROL_CARD = {
    "O": "Scan the raw N128 archive for empirical Betchov identity quantities.",
    "R": "Per-frame integral det(S), Pi = ω_i S_ij ω_j, and residual values from reconstructed strain.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed: reconstruction gaps or non-finite fields reduce to partial/missing status, never synthetic success.",
    "L": "Load raw velocity snapshots, reconstruct spectral derivatives, compute strain/vorticity per frame, integrate, and emit deterministic JSON.",
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion claim is introduced by this scan.",
    "F": "If raw velocity is unavailable or frame reconstruction is incomplete, the scan degrades with explicit non-ok statuses and diagnostics.",
}


@dataclass(frozen=True)
class VelocityBundle:
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    frame_count: int
    has_frame_axis: bool
    source: str
    source_path: Path


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be non-negative")
    return parsed


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        parsed = float(value)
    elif isinstance(value, np.generic):
        parsed = float(value.item())
    elif isinstance(value, str):
        try:
            parsed = float(value)
        except ValueError:
            return None
    else:
        return None
    if not math.isfinite(parsed):
        return None
    return parsed


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _coerce_metadata_scalar(value: Any) -> str | float | None:
    if isinstance(value, (bytes, bytearray, np.bytes_)):
        return bytes(value).decode("utf-8")
    if isinstance(value, np.ndarray):
        if value.shape == ():
            return _coerce_metadata_scalar(value.item())
        if value.ndim == 1 and value.size == 1:
            return _coerce_metadata_scalar(value.reshape(-1)[0].item())
        return None
    if isinstance(value, np.generic):
        return _coerce_metadata_scalar(value.item())
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        return value
    return None


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
            metadata_raw = _coerce_metadata_scalar(payload["meta_json"])
            if metadata_raw is None:
                raise TypeError(f"unsupported meta_json type: {type(payload['meta_json']).__name__}")
            metadata = json.loads(str(metadata_raw))
        except Exception as exc:  # pragma: no cover
            raise ValueError(f"meta_json exists but is not parseable JSON: {exc}") from exc
        if isinstance(metadata, dict):
            for key in ("grid_spacing", "dx", "dh", "domain_length", "length", "L", "domain", "N"):
                if key in metadata and key not in payload:
                    payload[key] = np.asarray(metadata[key])
    return payload


def _read_scalar_metadata(data: dict[str, np.ndarray], names: tuple[str, ...]) -> tuple[float | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape == ():
            scalar = value.item()
        elif value.ndim == 1 and value.size == 1:
            scalar = value.reshape(-1)[0].item()
        else:
            continue
        if isinstance(scalar, (bytes, bytearray, np.bytes_)):
            scalar = bytes(scalar).decode("utf-8")
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        try:
            parsed = float(scalar)
        except (TypeError, ValueError):
            continue
        if not math.isfinite(parsed):
            continue
        return parsed, name
    return None, None


def _infer_domain_length(data: dict[str, np.ndarray], n: int, warnings: list[str]) -> float:
    domain_length, domain_key = _read_scalar_metadata(data, ("domain_length", "length", "L", "domain"))
    if domain_length is not None:
        if domain_length <= 0.0:
            raise ValueError("domain_length must be positive")
        return float(domain_length)

    spacing, spacing_key = _read_scalar_metadata(data, ("grid_spacing", "dx", "dh"))
    if spacing is not None:
        if spacing <= 0.0:
            raise ValueError("grid spacing must be positive")
        inferred = float(spacing) * n
        warnings.append(
            f"domain_length missing; inferred from {spacing_key} as {inferred} (grid spacing * N)"
        )
        return inferred

    fallback = 2.0 * math.pi
    warnings.append(f"domain metadata missing; defaulting to fallback length {fallback}")
    return fallback


def _to_real_array(value: Any, label: str) -> np.ndarray:
    array = np.asarray(value)
    if np.iscomplexobj(array):
        imag_max = float(np.max(np.abs(np.imag(array)))) if array.size else 0.0
        real_scale = float(np.max(np.abs(np.real(array)))) if array.size else 1.0
        scale = max(1.0, real_scale)
        if imag_max > 1.0e-8 * scale:
            raise ValueError(f"{label} has non-negligible complex residue: max_imag={imag_max:.3e}")
        array = np.real(array)
    return np.asarray(array, dtype=np.float64)


def _select_velocity_bundle(data: dict[str, np.ndarray], warnings: list[str], archive_path: Path) -> VelocityBundle:
    if "velocity_snapshots" in data:
        velocity = _to_real_array(data["velocity_snapshots"], "velocity_snapshots")
        if velocity.ndim == 5:
            if velocity.shape[-1] != 3:
                if velocity.shape[1] == 3:
                    warnings.append("velocity_snapshots detected with axis-1 component layout")
                    if velocity.shape[0] <= 0:
                        raise ValueError("velocity_snapshots has no frame axis")
                    return VelocityBundle(
                        u=np.asarray(velocity[:, 0], dtype=np.float64),
                        v=np.asarray(velocity[:, 1], dtype=np.float64),
                        w=np.asarray(velocity[:, 2], dtype=np.float64),
                        frame_count=int(velocity.shape[0]),
                        has_frame_axis=True,
                        source="velocity_snapshots",
                        source_path=archive_path,
                    )
                raise ValueError(f"velocity_snapshots must have trailing component axis 3, got {velocity.shape!r}")
            if velocity.shape[0] <= 0:
                raise ValueError("velocity_snapshots has no frame axis")
            u = np.asarray(velocity[..., 0], dtype=np.float64)
            v = np.asarray(velocity[..., 1], dtype=np.float64)
            w = np.asarray(velocity[..., 2], dtype=np.float64)
            return VelocityBundle(
                u=u,
                v=v,
                w=w,
                frame_count=int(velocity.shape[0]),
                has_frame_axis=True,
                source="velocity_snapshots",
                source_path=archive_path,
            )
        if velocity.ndim == 4:
            if velocity.shape[-1] == 3:
                warnings.append("velocity_snapshots detected with final component axis")
                return VelocityBundle(
                    u=np.asarray(velocity[..., 0], dtype=np.float64),
                    v=np.asarray(velocity[..., 1], dtype=np.float64),
                    w=np.asarray(velocity[..., 2], dtype=np.float64),
                    frame_count=1,
                    has_frame_axis=False,
                    source="velocity_snapshots",
                    source_path=archive_path,
                )
            if velocity.shape[0] == 3:
                warnings.append("velocity_snapshots detected with leading component axis")
                return VelocityBundle(
                    u=np.asarray(velocity[0], dtype=np.float64),
                    v=np.asarray(velocity[1], dtype=np.float64),
                    w=np.asarray(velocity[2], dtype=np.float64),
                    frame_count=1,
                    has_frame_axis=False,
                    source="velocity_snapshots",
                    source_path=archive_path,
                )
            raise ValueError(f"unsupported velocity_snapshots layout {velocity.shape!r}")
        raise ValueError(f"unsupported velocity_snapshots rank {velocity.ndim}")

    if all(name in data for name in ("u", "v", "w")):
        u = _to_real_array(data["u"], "u")
        v = _to_real_array(data["v"], "v")
        w = _to_real_array(data["w"], "w")
        if not (u.shape == v.shape == w.shape):
            raise ValueError(f"u/v/w shape mismatch: {u.shape!r}, {v.shape!r}, {w.shape!r}")
        if u.ndim == 3:
            return VelocityBundle(
                u=u,
                v=v,
                w=w,
                frame_count=1,
                has_frame_axis=False,
                source="u/v/w",
                source_path=archive_path,
            )
        if u.ndim == 4:
            if int(u.shape[0]) <= 0:
                raise ValueError("u/v/w have empty frame axis")
            warnings.append("u/v/w detected with leading frame axis")
            return VelocityBundle(
                u=u,
                v=v,
                w=w,
                frame_count=int(u.shape[0]),
                has_frame_axis=True,
                source="u/v/w",
                source_path=archive_path,
            )
        raise ValueError(f"u/v/w must be 3D or leading-frame 4D, got {u.ndim}D")

    if all(name in data for name in ("u_hat", "v_hat", "w_hat")):
        raw_fields: list[np.ndarray] = []
        for name in ("u_hat", "v_hat", "w_hat"):
            spectral = np.asarray(data[name], dtype=np.complex128)
            if spectral.ndim == 3:
                physical = np.fft.ifftn(spectral, axes=(0, 1, 2)).real
            elif spectral.ndim == 4:
                if spectral.shape[0] == 1:
                    warnings.append(f"{name} has singleton leading frame axis; dropping it")
                    physical = np.fft.ifftn(spectral[0], axes=(0, 1, 2)).real
                else:
                    physical = np.fft.ifftn(spectral, axes=(1, 2, 3)).real
            else:
                raise ValueError(f"{name} must be 3D or leading-frame 4D, got {spectral.ndim}D")
            raw_fields.append(physical)
        u, v, w = [_to_real_array(field, name) for field, name in zip(raw_fields, ("u_hat", "v_hat", "w_hat"))]
        if not (u.shape == v.shape == w.shape):
            raise ValueError(f"u_hat/v_hat/w_hat physical shape mismatch: {u.shape!r}, {v.shape!r}, {w.shape!r}")
        if u.ndim == 3:
            return VelocityBundle(
                u=u,
                v=v,
                w=w,
                frame_count=1,
                has_frame_axis=False,
                source="u_hat/v_hat/w_hat",
                source_path=archive_path,
            )
        if u.ndim == 4:
            warnings.append("u_hat/v_hat/w_hat detected with leading frame axis")
            return VelocityBundle(
                u=u,
                v=v,
                w=w,
                frame_count=int(u.shape[0]),
                has_frame_axis=True,
                source="u_hat/v_hat/w_hat",
                source_path=archive_path,
            )
        raise ValueError(f"physical u_hat/v_hat/w_hat must be 3D or 4D, got {u.ndim}D")

    raise FileNotFoundError(
        "raw archive is missing velocity fields; expected one of velocity_snapshots or u/v/w or u_hat/v_hat/w_hat"
    )


def _frame_velocity(bundle: VelocityBundle, frame: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if bundle.has_frame_axis:
        if frame < 0 or frame >= bundle.frame_count:
            raise IndexError(f"snapshot {frame} is outside [0, {bundle.frame_count})")
        return (
            np.asarray(bundle.u[frame], dtype=np.float64),
            np.asarray(bundle.v[frame], dtype=np.float64),
            np.asarray(bundle.w[frame], dtype=np.float64),
        )
    if frame != 0:
        raise IndexError("archive has no frame axis but frame was requested")
    return (
        np.asarray(bundle.u, dtype=np.float64),
        np.asarray(bundle.v, dtype=np.float64),
        np.asarray(bundle.w, dtype=np.float64),
    )


def _axis_wavenumbers(n: int, domain_length: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    k = 2.0 * math.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    return k.reshape(n, 1, 1), k.reshape(1, n, 1), k.reshape(1, 1, n)


def _spectral_derivative(field: np.ndarray, axis: int, kx: np.ndarray, ky: np.ndarray, kz: np.ndarray) -> np.ndarray:
    transformed = np.fft.fftn(field, axes=(0, 1, 2))
    if axis == 0:
        return np.fft.ifftn(1j * kx * transformed, axes=(0, 1, 2)).real
    if axis == 1:
        return np.fft.ifftn(1j * ky * transformed, axes=(0, 1, 2)).real
    if axis == 2:
        return np.fft.ifftn(1j * kz * transformed, axes=(0, 1, 2)).real
    raise ValueError(f"axis must be 0,1,2; got {axis}")


def _validate_cube(field: np.ndarray, name: str) -> tuple[np.ndarray, int]:
    arr = np.asarray(field)
    if arr.ndim != 3:
        raise ValueError(f"{name} must be cubic 3D after frame extraction, got {arr.shape!r}")
    n = int(arr.shape[0])
    if n <= 1 or int(arr.shape[1]) != n or int(arr.shape[2]) != n:
        raise ValueError(f"{name} must be cubic with n>1, got {arr.shape!r}")
    return arr, n


def _compute_det_and_pi(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray]:
    u, n = _validate_cube(u, "u")
    v, _ = _validate_cube(v, "v")
    w, _ = _validate_cube(w, "w")
    if not (u.shape == v.shape == w.shape):
        raise ValueError(f"velocity component shapes differ: {u.shape!r}, {v.shape!r}, {w.shape!r}")

    kx, ky, kz = _axis_wavenumbers(n, domain_length)
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

    det_s = (
        s11 * (s22 * s33 - s23 * s23)
        - s12 * (s12 * s33 - s23 * s13)
        + s13 * (s12 * s23 - s22 * s13)
    )

    omega_x = dw_dy - dv_dz
    omega_y = du_dz - dw_dx
    omega_z = dv_dx - du_dy
    omega_s_omega = (
        s11 * omega_x * omega_x
        + s22 * omega_y * omega_y
        + s33 * omega_z * omega_z
        + 2.0 * (s12 * omega_x * omega_y + s13 * omega_x * omega_z + s23 * omega_y * omega_z)
    )
    return np.asarray(det_s, dtype=np.float64), np.asarray(omega_s_omega, dtype=np.float64)


def _integral(values: np.ndarray, domain_length: float, valid: np.ndarray) -> tuple[float, int]:
    valid = np.asarray(valid, dtype=bool)
    if valid.shape != values.shape:
        raise ValueError("valid mask shape mismatch")
    selected = np.asarray(values, dtype=np.float64)[valid]
    selected = selected[np.isfinite(selected)]
    if selected.size == 0:
        return 0.0, 0
    n = int(values.shape[0])
    cell_volume = (float(domain_length) / float(n)) ** 3
    return float(np.sum(selected, dtype=np.float64) * cell_volume), int(selected.size)


def _compute_frame_rows(
    slot: int,
    snapshot: int,
    bundle: VelocityBundle,
    domain_length: float,
    warnings: list[str],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.source_path),
        "velocity_source": bundle.source,
    }

    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        det_s, pi_density = _compute_det_and_pi(u, v, w, domain_length)
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_evaluation:{exc}"]
        return ERROR_STATUS, row

    finite = np.isfinite(det_s) & np.isfinite(pi_density)
    valid_count = int(np.count_nonzero(finite))
    cell_count = int(det_s.size)
    row["cell_count"] = cell_count
    row["valid_cell_count"] = valid_count

    if cell_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["empty frame"]
        return ERROR_STATUS, row
    if valid_count == 0:
        row["status"] = ERROR_STATUS
        row["errors"] = ["frame has no finite det(S) or Pi density cells"]
        return ERROR_STATUS, row

    if valid_count != cell_count:
        warnings.append(f"frame {slot}: excluding {cell_count - valid_count} non-finite cells")

    integral_det, n_det = _integral(det_s, domain_length, finite)
    integral_pi, n_pi = _integral(pi_density, domain_length, finite)
    if n_det != n_pi:
        warnings.append(
            f"frame {slot}: finite-cell counts differ detS={n_det} vs Pi={n_pi}; integrating on per-field finite masks"
        )

    det_finite = det_s[finite]
    pi_finite = pi_density[finite]
    residual = float(integral_det + 0.25 * integral_pi)
    relative_scale = abs(integral_det) + 0.25 * abs(integral_pi) + DEFAULT_EPS
    relation_relative = abs(residual) / relative_scale

    status = OK_STATUS
    if valid_count != cell_count:
        status = PARTIAL_STATUS

    row.update(
        {
            "status": status,
            "finite_fraction": float(valid_count) / float(cell_count),
            "integral_detS": float(integral_det),
            "integral_pi": float(integral_pi),
            "relation_residual": residual,
            "relation_residual_abs": abs(residual),
            "relation_residual_relative": float(relation_relative),
            "detS_min": float(np.min(det_finite)),
            "detS_max": float(np.max(det_finite)),
            "pi_density_min": float(np.min(pi_finite)),
            "pi_density_max": float(np.max(pi_finite)),
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
        "global_integral_detS": 0.0,
        "global_integral_pi": 0.0,
        "global_relation_residual": 0.0,
        "global_relation_residual_abs": 0.0,
        "global_relation_residual_relative": 0.0,
        "global_relation_expected_from_totals": 0.0,
        "global_detS_min": None,
        "global_detS_max": None,
        "global_pi_density_min": None,
        "global_pi_density_max": None,
    }

    norm = 0.0
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
        aggregate["global_valid_cell_count"] += int(row.get("valid_cell_count", 0))

        det_value = _coerce_float(row.get("integral_detS"))
        pi_value = _coerce_float(row.get("integral_pi"))
        residual = _coerce_float(row.get("relation_residual"))
        if det_value is not None:
            aggregate["global_integral_detS"] += det_value
        if pi_value is not None:
            aggregate["global_integral_pi"] += pi_value
        if residual is not None:
            aggregate["global_relation_residual"] += residual

        det_min = _coerce_float(row.get("detS_min"))
        det_max = _coerce_float(row.get("detS_max"))
        pi_min = _coerce_float(row.get("pi_density_min"))
        pi_max = _coerce_float(row.get("pi_density_max"))

        if det_min is not None and (
            aggregate["global_detS_min"] is None or det_min < aggregate["global_detS_min"]
        ):
            aggregate["global_detS_min"] = det_min
        if det_max is not None and (
            aggregate["global_detS_max"] is None or det_max > aggregate["global_detS_max"]
        ):
            aggregate["global_detS_max"] = det_max
        if pi_min is not None and (
            aggregate["global_pi_density_min"] is None or pi_min < aggregate["global_pi_density_min"]
        ):
            aggregate["global_pi_density_min"] = pi_min
        if pi_max is not None and (
            aggregate["global_pi_density_max"] is None or pi_max > aggregate["global_pi_density_max"]
        ):
            aggregate["global_pi_density_max"] = pi_max

        norm += (abs(det_value) if det_value is not None else 0.0) + 0.25 * (
            abs(pi_value) if pi_value is not None else 0.0
        )

    aggregate["global_relation_expected_from_totals"] = float(
        aggregate["global_integral_detS"] + 0.25 * aggregate["global_integral_pi"]
    )
    aggregate["global_relation_residual_abs"] = abs(float(aggregate["global_relation_residual"]))
    aggregate["global_relation_residual_relative"] = (
        float(aggregate["global_relation_residual"]) / norm if norm > DEFAULT_EPS else 0.0
    )
    return aggregate


def _select_frames(frame_count: int, requested: int | None, limit: int | None) -> list[int]:
    if frame_count <= 0:
        return []
    if requested is not None:
        return [requested] if requested < frame_count else []
    frames = list(range(frame_count))
    return frames if limit is None else frames[:limit]


def _compute_status(rows: list[dict[str, Any]], errors: list[str]) -> str:
    if errors:
        return ERROR_STATUS
    if not rows:
        return MISSING_REQUIRED_STATUS
    if any(row.get("status") == ERROR_STATUS for row in rows):
        return ERROR_STATUS
    if any(row.get("status") == MISSING_REQUIRED_STATUS for row in rows):
        return PARTIAL_STATUS
    if any(row.get("status") == PARTIAL_STATUS for row in rows):
        return PARTIAL_STATUS
    return OK_STATUS


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="raw archive with velocity snapshots")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="single frame index")
    parser.add_argument("--frame-limit", type=_positive_int, default=None, help="max number of frames from the start")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="output JSON path")
    parser.add_argument("--pretty", action="store_true", help="pretty-print output JSON")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    errors: list[str] = []
    warnings: list[str] = []

    try:
        data = _load_npz(args.raw_archive)
        bundle = _select_velocity_bundle(data, warnings, args.raw_archive)
        n = int(bundle.u.shape[-1]) if bundle.has_frame_axis else int(bundle.u.shape[0])
        domain_length = _infer_domain_length(data, n, warnings)
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
                "zero_tolerance": DEFAULT_ZERO_EPS,
            },
            "rows": [],
            "aggregate": {
                "processed_frames": 0,
                "ok_frames": 0,
                "partial_frames": 0,
                "missing_frames": 0,
                "error_frames": 0,
                "global_cell_count": 0,
                "global_valid_cell_count": 0,
                "global_integral_detS": 0.0,
                "global_integral_pi": 0.0,
                "global_relation_residual": 0.0,
                "global_relation_residual_abs": 0.0,
                "global_relation_residual_relative": 0.0,
                "global_relation_expected_from_totals": 0.0,
                "global_detS_min": None,
                "global_detS_max": None,
                "global_pi_density_min": None,
                "global_pi_density_max": None,
            },
            "errors": [str(exc)],
            "warnings": [],
            "changed_files": [str(args.output)],
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, pretty=args.pretty))
        return 1

    frame_indices = _select_frames(bundle.frame_count, args.frame, args.frame_limit)
    if not frame_indices and args.frame is not None:
        errors.append(f"requested frame {args.frame} out of range for {bundle.frame_count} frames")
    rows: list[dict[str, Any]] = []

    for slot, snapshot in enumerate(frame_indices):
        status, row = _compute_frame_rows(
            slot=slot,
            snapshot=snapshot,
            bundle=bundle,
            domain_length=domain_length,
            warnings=warnings,
        )
        rows.append(row)

    aggregate = _build_aggregate(rows)
    status = _compute_status(rows, errors)
    if status == PARTIAL_STATUS:
        # check residual consistency on each row and aggregate as a quality sanity check.
        for row in rows:
            row_det = _coerce_float(row.get("integral_detS"))
            row_pi = _coerce_float(row.get("integral_pi"))
            row_residual = _coerce_float(row.get("relation_residual"))
            if row_det is None or row_pi is None or row_residual is None:
                continue
            expected = row_det + 0.25 * row_pi
            if abs(row_residual - expected) > CHECK_TOLERANCE:
                warnings.append(
                    f"frame {row.get('frame', '?')}: row residual mismatch {row_residual} vs expected {expected}"
                )

        aggregate_expected = _coerce_float(aggregate.get("global_relation_expected_from_totals"))
        aggregate_residual = _coerce_float(aggregate.get("global_relation_residual"))
        if aggregate_expected is not None and aggregate_residual is not None:
            if abs(aggregate_residual - aggregate_expected) > CHECK_TOLERANCE:
                warnings.append(
                    f"aggregate residual mismatch {aggregate_residual} vs expected {aggregate_expected}"
                )

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
            "velocity_source": bundle.source,
            "source_path": str(bundle.source_path),
            "domain_length": float(domain_length),
        },
        "rows": rows,
        "aggregate": aggregate,
        "errors": errors,
        "warnings": warnings,
        "changed_files": [str(args.output)],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
