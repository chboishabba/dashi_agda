#!/usr/bin/env python3
"""Sard-style empirical λ2 boundary regularity proxy scan for N128 archives.

This script is intentionally empirical/non-promoting. It either loads ``lambda2``
from derived data or reconstructs it from raw velocity fields, then measures
``|grad lambda2|`` on cells satisfying ``|lambda2| <= band``.

No analytic theorem is inferred from this output.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_lambda2_boundary_regularity_scan.py"
CONTRACT = "ns_lambda2_boundary_regularity_scan"
ROUTE_DECISION = "FAIL_CLOSED_LAMBDA2_BOUNDARY_REGULARITY_SCAN"

OK_STATUS = "ok"
DEGRADED_STATUS = "degraded"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"

DEFAULT_FRAME_LIMIT = 13
DEFAULT_LAMBDA2_BAND = 1.0e-3
DEFAULT_GRAD_THRESHOLDS = (0.05, 0.1, 0.5, 1.0)
DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_lambda2_boundary_regularity_scan_N128_20260620.json"
)
DEFAULT_DOMAIN_LENGTH = 2.0 * math.pi

LAMBDA2_KEYS = (
    "lambda2",
    "lambda2_field",
    "lambda2_values",
    "smallest_strain_eigenvalue",
)

CONTROL_CARD = {
    "O": "Construct an empirical regularity proxy near the λ2=0 boundary.",
    "R": (
        "Load or reconstruct λ2 per frame, compute |grad λ2| on a small |lambda2| band, "
        "and emit per-frame counts/fractions versus chosen thresholds plus aggregate summaries."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Prefer derived λ2; reconstruct from raw velocity only when derived is absent. "
        "Fail-closed on missing/corrupt inputs."
    ),
    "L": (
        "Resolve candidate N128 archives, parse scale metadata when present, compute spectral "
        "gradients, and emit deterministic per-frame rows plus aggregate diagnostics."
    ),
    "P": ROUTE_DECISION,
    "G": "This output is an empirical proxy only and does not promote a regularity claim.",
    "F": "Sard regularity is an analytic statement; this scan is a numerical proxy only.",
}


@dataclass(frozen=True)
class ArchiveBundle:
    path: Path
    data: dict[str, np.ndarray]
    frame_count: int


@dataclass(frozen=True)
class RawBundle:
    path: Path
    data: dict[str, np.ndarray]
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    has_frame_axis: bool
    frame_count: int
    domain_length: float


@dataclass(frozen=True)
class FrameSource:
    slot: int
    snapshot: int
    data: dict[str, np.ndarray]
    path: Path
    frame_arg: int | None
    source_label: str


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return parsed


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("must be a nonnegative integer")
    return parsed


def _positive_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed <= 0.0:
        raise argparse.ArgumentTypeError("must be finite and positive")
    return parsed


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--raw-archive",
        type=Path,
        default=DEFAULT_RAW_ARCHIVE,
        help="Raw archive used for λ2 reconstruction fallback.",
    )
    parser.add_argument(
        "--derived-archive",
        type=Path,
        default=None,
        help="Derived archive or directory containing λ2.",
    )
    parser.add_argument(
        "--input-dir",
        type=Path,
        default=Path("."),
        help="Fallback search root for raw/derived archives.",
    )
    parser.add_argument(
        "--frame-limit",
        type=_positive_int,
        default=DEFAULT_FRAME_LIMIT,
        help="Maximum number of frames.",
    )
    parser.add_argument(
        "--frame",
        type=_nonnegative_int,
        default=None,
        help="Process only one frame index.",
    )
    parser.add_argument(
        "--lambda2-band",
        type=_positive_float,
        default=DEFAULT_LAMBDA2_BAND,
        help="Boundary slab width in |lambda2|.",
    )
    parser.add_argument(
        "--grad-threshold",
        type=float,
        nargs="+",
        default=list(DEFAULT_GRAD_THRESHOLDS),
        help="Thresholds for |grad lambda2| counts on the boundary band.",
    )
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="Optional domain side-length override.",
    )
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    parser.add_argument("--json", action="store_true", help="Also print JSON to stdout.")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _normalize_key(value: str) -> str:
    return "".join(ch.lower() for ch in value if ch.isalnum())


def _find_field(data: dict[str, np.ndarray], aliases: tuple[str, ...]) -> tuple[str | None, np.ndarray | None]:
    for alias in aliases:
        if alias in data:
            return alias, np.asarray(data[alias])
    normalized = {_normalize_key(alias): alias for alias in aliases}
    for key, value in data.items():
        if isinstance(key, str) and _normalize_key(key) in normalized:
            return key, np.asarray(value)
    return None, None


def _coerce_thresholds(values: list[float]) -> list[float]:
    ordered: list[float] = []
    seen: set[float] = set()
    for raw in values:
        if not math.isfinite(raw):
            continue
        value = float(raw)
        if value < 0.0:
            continue
        if value not in seen:
            ordered.append(value)
            seen.add(value)
    ordered.sort()
    return ordered


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    if not path.exists():
        raise FileNotFoundError(f"archive missing: {path}")
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in payload:
        try:
            raw_meta = payload["meta_json"]
            if isinstance(raw_meta, np.ndarray) and raw_meta.shape == ():
                raw_meta = raw_meta.item()
            if isinstance(raw_meta, np.ndarray) and raw_meta.ndim == 0:
                raw_meta = raw_meta.reshape(()).item()
            if isinstance(raw_meta, np.ndarray) and raw_meta.size == 1:
                raw_meta = raw_meta.reshape(-1)[0].item()
            if isinstance(raw_meta, (bytes, bytearray, np.bytes_)):
                raw_meta = bytes(raw_meta).decode("utf-8")
            metadata = json.loads(str(raw_meta))
        except Exception as exc:  # pragma: no cover - defensive
            raise ValueError(f"meta_json exists but cannot be parsed: {exc}") from exc
        if isinstance(metadata, dict):
            for key in ("domain_length", "grid_spacing", "dx", "dh", "length", "L", "domain", "N"):
                if key in metadata and key not in payload:
                    payload[key] = np.asarray(metadata[key])
    return payload


def _scalar_metadata(data: dict[str, np.ndarray], *names: str) -> tuple[Any | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape == ():
            scalar = value.item()
        elif value.ndim == 1 and value.size == 1:
            scalar = value.reshape(()).item()
        else:
            continue
        if isinstance(scalar, (bytes, bytearray, np.bytes_)):
            scalar = bytes(scalar).decode("utf-8")
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        return scalar, name
    return None, None


def _finite_scalar_metadata(data: dict[str, np.ndarray], *names: str) -> tuple[float | None, str | None]:
    scalar, key = _scalar_metadata(data, *names)
    if scalar is None:
        return None, None
    try:
        value = float(scalar)
    except (TypeError, ValueError):
        return None, key
    return (value, key) if math.isfinite(value) else (None, key)


def _estimate_frame_count_from_field(name: str, value: np.ndarray) -> int | None:
    arr = np.asarray(value)
    if arr.ndim == 5:
        return int(arr.shape[0])
    if arr.ndim == 4:
        if name == "velocity_snapshots":
            if int(arr.shape[-1]) == 3:
                return 1
            if int(arr.shape[1]) == 3:
                return int(arr.shape[0])
            return 1 if int(arr.shape[0]) == 1 else int(arr.shape[0])
        if name in ("u", "v", "w", "u_hat", "v_hat", "w_hat"):
            return int(arr.shape[0]) if int(arr.shape[0]) > 1 else 1
        return int(arr.shape[0])
    if arr.ndim == 3:
        return 1
    return None


def _extract_frame_count(data: dict[str, np.ndarray]) -> int:
    frame_counts: set[int] = set()
    for name in ("lambda2", "velocity_snapshots", "u", "v", "w", "u_hat", "v_hat", "w_hat"):
        if name not in data:
            continue
        count = _estimate_frame_count_from_field(name, data[name])
        if count is None:
            continue
        if count <= 0:
            raise ValueError(f"{name} has invalid frame count {count}")
        frame_counts.add(count)
    if not frame_counts:
        raise ValueError("archive has no usable frame fields")
    if len(frame_counts) > 1:
        raise ValueError(f"inconsistent frame counts: {sorted(frame_counts)!r}")
    return frame_counts.pop()


def _load_bundle(path: Path) -> ArchiveBundle:
    data = _load_npz(path)
    frame_count = _extract_frame_count(data)
    return ArchiveBundle(path=path, data=data, frame_count=frame_count)


def _frame_sort_key(path: Path) -> tuple[int, str]:
    match = re.search(r"(?:^|[._-])(?:frame)?[._-]?(\d+)(?:$|[._-])", path.stem.lower())
    if match is not None:
        return int(match.group(1)), path.name
    return 10**12, path.name


def _candidate_score(path: Path, kind: str) -> tuple[int, str]:
    stem = path.stem.lower()
    score = 0
    if kind == "raw":
        if "raw" in stem:
            score += 3
        if "pressure" in stem or "ns3d" in stem:
            score += 2
        if "velocity" in stem:
            score += 1
    else:
        if "derived" in stem or "tensor" in stem:
            score += 3
        if "lambda2" in stem or "boundary" in stem:
            score += 2
    if "n128" in stem:
        score += 1
    if "frame" in stem:
        score += 1
    return score, path.name


def _find_candidate_npz(directory: Path, kind: str) -> Path:
    if not directory.exists():
        raise FileNotFoundError(f"directory missing: {directory}")
    if directory.is_file():
        if directory.suffix.lower() != ".npz":
            raise ValueError(f"expected .npz path, got {directory}")
        return directory
    candidates = [path for path in directory.rglob("*.npz") if path.is_file()]
    if not candidates:
        raise FileNotFoundError(f"no .npz under {directory}")
    scored = sorted((_candidate_score(path, kind), path) for path in candidates)
    best = scored[-1][0][0]
    winners = [path for score, path in scored if score[0] == best]
    return sorted(winners)[0]


def _to_real_array(value: Any, label: str) -> np.ndarray:
    arr = np.asarray(value)
    if np.iscomplexobj(arr):
        imag = float(np.max(np.abs(np.imag(arr)))) if arr.size else 0.0
        real_scale = float(np.max(np.abs(np.real(arr)))) if arr.size else 1.0
        if imag > 1.0e-8 * max(1.0, real_scale):
            raise ValueError(f"{label} has non-negligible imaginary part ({imag})")
        arr = np.real(arr)
    return np.asarray(arr, dtype=np.float64)


def _resolve_domain_length(
    raw_data: dict[str, np.ndarray] | None,
    derived_data: dict[str, np.ndarray] | None,
    override: float | None,
    n: int,
    warnings: list[str],
) -> tuple[float, str]:
    if override is not None:
        if not math.isfinite(override) or override <= 0.0:
            raise ValueError("--domain-length override must be finite positive")
        return float(override), "override"

    raw_len, raw_key = _finite_scalar_metadata(raw_data or {}, "domain_length", "length", "L", "domain")
    derived_len, derived_key = (
        _finite_scalar_metadata(derived_data or {}, "domain_length", "length", "L", "domain")
        if derived_data is not None
        else (None, None)
    )
    raw_spacing, raw_spacing_key = _finite_scalar_metadata(raw_data or {}, "grid_spacing", "dx", "dh")
    derived_spacing, derived_spacing_key = (
        _finite_scalar_metadata(derived_data or {}, "grid_spacing", "dx", "dh")
        if derived_data is not None
        else (None, None)
    )

    if raw_len is not None and derived_len is not None and not math.isclose(
        raw_len, derived_len, rel_tol=1.0e-12, abs_tol=1.0e-12
    ):
        warnings.append(f"domain_length mismatch raw({raw_key})={raw_len} vs derived({derived_key})={derived_len}")

    if raw_len is not None and raw_len > 0.0:
        return float(raw_len), f"raw:{raw_key or 'domain_length'}"
    if derived_len is not None and derived_len > 0.0:
        return float(derived_len), f"derived:{derived_key or 'domain_length'}"
    if raw_spacing is not None and raw_spacing > 0.0:
        warnings.append("domain_length inferred from raw grid_spacing")
        return float(raw_spacing) * float(n), "raw:grid_spacing*N"
    if derived_spacing is not None and derived_spacing > 0.0:
        warnings.append("domain_length inferred from derived grid_spacing")
        return float(derived_spacing) * float(n), "derived:grid_spacing*N"
    warnings.append("domain metadata unavailable; using fallback 2π")
    return DEFAULT_DOMAIN_LENGTH, "fallback:2pi"


def _axis_wavenumbers(n: int, domain_length: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    k = 2.0 * math.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    return k.reshape(n, 1, 1), k.reshape(1, n, 1), k.reshape(1, 1, n)


def _spectral_derivative(field: np.ndarray, axis: int, kx: np.ndarray, ky: np.ndarray, kz: np.ndarray) -> np.ndarray:
    spec = np.fft.fftn(field, axes=(0, 1, 2))
    if axis == 0:
        return np.fft.ifftn(1j * kx * spec, axes=(0, 1, 2)).real
    if axis == 1:
        return np.fft.ifftn(1j * ky * spec, axes=(0, 1, 2)).real
    if axis == 2:
        return np.fft.ifftn(1j * kz * spec, axes=(0, 1, 2)).real
    raise ValueError(f"axis must be 0, 1, or 2; got {axis}")


def _gradient_magnitude(field: np.ndarray, domain_length: float) -> np.ndarray:
    if not math.isfinite(domain_length) or domain_length <= 0.0:
        raise ValueError("domain_length must be finite positive")
    arr = np.asarray(field, dtype=np.float64)
    if arr.ndim != 3:
        raise ValueError(f"field must be 3D, got {arr.shape!r}")
    n = int(arr.shape[0])
    if n <= 1 or int(arr.shape[1]) != n or int(arr.shape[2]) != n:
        raise ValueError(f"field must be cubic n>1, got {arr.shape!r}")
    kx, ky, kz = _axis_wavenumbers(n, domain_length)
    gx = _spectral_derivative(arr, 0, kx, ky, kz)
    gy = _spectral_derivative(arr, 1, kx, ky, kz)
    gz = _spectral_derivative(arr, 2, kx, ky, kz)
    return np.sqrt(gx * gx + gy * gy + gz * gz)


def _select_velocity_components(
    data: dict[str, np.ndarray],
    warnings: list[str],
) -> tuple[np.ndarray, np.ndarray, np.ndarray, bool]:
    if "velocity_snapshots" in data:
        velocity = _to_real_array(data["velocity_snapshots"], "velocity_snapshots")
        if velocity.ndim == 5:
            if int(velocity.shape[-1]) == 3:
                warnings.append("velocity_snapshots detected on final component axis")
                return (
                    velocity[..., 0],
                    velocity[..., 1],
                    velocity[..., 2],
                    int(velocity.shape[0]) > 1,
                )
            if int(velocity.shape[1]) == 3:
                warnings.append("velocity_snapshots detected on axis 1")
                return (
                    velocity[:, 0, ...],
                    velocity[:, 1, ...],
                    velocity[:, 2, ...],
                    int(velocity.shape[0]) > 1,
                )
            raise ValueError(f"velocity_snapshots unsupported 5D layout: {velocity.shape!r}")
        if velocity.ndim == 4:
            if int(velocity.shape[-1]) == 3:
                warnings.append("velocity_snapshots detected no frame axis (final component axis)")
                return (
                    velocity[..., 0],
                    velocity[..., 1],
                    velocity[..., 2],
                    False,
                )
            if int(velocity.shape[0]) == 3:
                warnings.append("velocity_snapshots detected no frame axis (leading component axis)")
                return (
                    velocity[0],
                    velocity[1],
                    velocity[2],
                    False,
                )
            raise ValueError(f"velocity_snapshots unsupported 4D layout: {velocity.shape!r}")
        raise ValueError(f"velocity_snapshots unsupported rank: {velocity.ndim}")

    if all(name in data for name in ("u", "v", "w")):
        u = _to_real_array(data["u"], "u")
        v = _to_real_array(data["v"], "v")
        w = _to_real_array(data["w"], "w")
        if not (u.shape == v.shape == w.shape):
            raise ValueError(f"u/v/w shape mismatch: {u.shape!r}, {v.shape!r}, {w.shape!r}")
        if u.ndim == 3:
            return u, v, w, False
        if u.ndim == 4:
            if int(u.shape[0]) == 1:
                return u[0], v[0], w[0], False
            return u, v, w, True
        raise ValueError(f"u/v/w unsupported rank: {u.ndim}")

    if all(name in data for name in ("u_hat", "v_hat", "w_hat")):
        fields: list[np.ndarray] = []
        frame_axes: list[bool] = []
        for name in ("u_hat", "v_hat", "w_hat"):
            spectral = np.asarray(data[name], dtype=np.complex128)
            if spectral.ndim == 3:
                frame_axes.append(False)
                fields.append(_to_real_array(np.fft.ifftn(spectral, axes=(0, 1, 2)).real, name))
            elif spectral.ndim == 4:
                if int(spectral.shape[0]) > 1:
                    frame_axes.append(True)
                    fields.append(_to_real_array(np.fft.ifftn(spectral, axes=(1, 2, 3)).real, name))
                elif int(spectral.shape[0]) == 1:
                    frame_axes.append(False)
                    fields.append(_to_real_array(np.fft.ifftn(spectral[0], axes=(0, 1, 2)).real, name))
                else:
                    raise ValueError(f"{name} frame axis invalid: {spectral.shape!r}")
            else:
                raise ValueError(f"{name} unsupported rank: {spectral.ndim}")
        if not (fields[0].shape == fields[1].shape == fields[2].shape):
            raise ValueError(
                f"u_hat/v_hat/w_hat physical shape mismatch: {fields[0].shape!r}, {fields[1].shape!r}, {fields[2].shape!r}"
            )
        return fields[0], fields[1], fields[2], any(frame_axes)

    raise FileNotFoundError(
        "raw archive missing velocity fields; expected velocity_snapshots, u/v/w, or u_hat/v_hat/w_hat"
    )


def _load_velocity_bundle(path: Path) -> RawBundle:
    data = _load_npz(path)
    u, v, w, has_frame_axis = _select_velocity_components(data, [])
    sample = u[0] if has_frame_axis else u
    if not (sample.ndim == 3):
        raise ValueError(f"velocity sample shape must be 3D, got {sample.shape!r}")
    n = int(sample.shape[0])
    if int(sample.shape[1]) != n or int(sample.shape[2]) != n or n <= 1:
        raise ValueError(f"velocity must be cubic n>1, got {sample.shape!r}")
    if not (np.isfinite(sample).all() and np.isfinite(v[0] if has_frame_axis else v).all() and np.isfinite(w[0] if has_frame_axis else w).all()):
        raise ValueError("raw velocity has non-finite values")

    dom, _ = _finite_scalar_metadata(data, "domain_length", "length", "L", "domain")
    if dom is None:
        spacing, _ = _finite_scalar_metadata(data, "grid_spacing", "dx", "dh")
        if spacing is not None:
            dom = float(spacing) * float(n)
    if dom is None or dom <= 0.0:
        dom = DEFAULT_DOMAIN_LENGTH

    return RawBundle(
        path=path,
        data=data,
        u=u,
        v=v,
        w=w,
        has_frame_axis=has_frame_axis,
        frame_count=(1 if not has_frame_axis else int(u.shape[0])),
        domain_length=float(dom),
    )


def _load_velocity_frame(bundle: RawBundle, frame: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if not bundle.has_frame_axis:
        if frame != 0:
            raise ValueError(f"raw archive has no frame axis; requested frame {frame}")
        return (
            np.asarray(bundle.u),
            np.asarray(bundle.v),
            np.asarray(bundle.w),
        )
    if frame < 0 or frame >= bundle.frame_count:
        raise ValueError(f"frame {frame} is outside [0, {bundle.frame_count})")
    return np.asarray(bundle.u[frame]), np.asarray(bundle.v[frame]), np.asarray(bundle.w[frame])


def _load_frame_field(name: str, value: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(value)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) == 1:
                arr = arr[0]
            else:
                raise ValueError(f"{name} has {arr.shape[0]} frames; use --frame")
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} out of range {arr.shape[0]}")
            arr = arr[frame]
    if arr.ndim == 5:
        if frame is None:
            if int(arr.shape[0]) == 1:
                arr = arr[0]
            else:
                raise ValueError(f"{name} has {arr.shape[0]} frames; use --frame")
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} out of range {arr.shape[0]}")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be 3D after frame selection, got {arr.shape!r}")
    return np.asarray(arr, dtype=np.float64)


def _load_lambda2_from_derived(data: dict[str, np.ndarray], frame: int | None) -> tuple[np.ndarray | None, str | None]:
    key, value = _find_field(data, LAMBDA2_KEYS)
    if value is None:
        return None, None
    return _load_frame_field(key or "lambda2", value, frame), f"derived:{key or 'lambda2'}"


def _lambda2_from_velocity(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    sample = np.asarray(u, dtype=np.float64)
    if not (sample.shape == np.asarray(v).shape == np.asarray(w).shape):
        raise ValueError(f"velocity component shape mismatch: {sample.shape!r}, {v.shape!r}, {w.shape!r}")
    if sample.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {sample.shape!r}")
    n = int(sample.shape[0])
    if int(sample.shape[1]) != n or int(sample.shape[2]) != n or n <= 1:
        raise ValueError(f"velocity must be cubic n>1, got {sample.shape!r}")
    if not (np.isfinite(sample).all() and np.isfinite(v).all() and np.isfinite(w).all()):
        raise ValueError("velocity components contain non-finite values")

    kx, ky, kz = _axis_wavenumbers(n, domain_length)
    du_dx = _spectral_derivative(sample, 0, kx, ky, kz)
    du_dy = _spectral_derivative(sample, 1, kx, ky, kz)
    du_dz = _spectral_derivative(sample, 2, kx, ky, kz)
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
    eigenvalues = np.linalg.eigvalsh(strain)
    return np.asarray(eigenvalues[..., 1], dtype=np.float64)


def _stats(values: np.ndarray) -> dict[str, float | None]:
    if values.size == 0:
        return {"min": None, "mean": None, "max": None}
    finite = values[np.isfinite(values)]
    if finite.size == 0:
        return {"min": None, "mean": None, "max": None}
    return {
        "min": float(np.min(finite)),
        "mean": float(np.mean(finite)),
        "max": float(np.max(finite)),
    }


def _load_derived_sources(path: Path, frame_limit: int, frame: int | None) -> list[FrameSource]:
    if not path.exists():
        raise FileNotFoundError(f"derived archive missing: {path}")
    sources: list[FrameSource] = []

    if path.is_file():
        bundle = _load_bundle(path)
        if frame is not None and frame >= bundle.frame_count:
            raise ValueError(f"requested frame {frame} out of derived range {bundle.frame_count}")
        selected = [frame] if frame is not None else list(range(min(frame_limit, bundle.frame_count)))
        for local in selected:
            sources.append(
                FrameSource(
                    slot=int(local),
                    snapshot=int(local),
                    data=bundle.data,
                    path=path,
                    frame_arg=local,
                    source_label=f"derived:{path.name}",
                )
            )
        return sources

    files = sorted(
        (item for item in path.iterdir() if item.is_file() and item.suffix.lower() == ".npz"),
        key=_frame_sort_key,
    )
    if not files:
        raise FileNotFoundError(f"derived directory has no .npz files: {path}")

    slot = 0
    for file_path in files:
        data = _load_npz(file_path)
        file_bundle = _load_bundle(file_path)
        for local in range(file_bundle.frame_count):
            if frame is not None and slot < frame:
                slot += 1
                continue
            if frame is not None and slot > frame:
                return sources
            sources.append(
                FrameSource(
                    slot=slot,
                    snapshot=slot,
                    data=data,
                    path=file_path,
                    frame_arg=local,
                    source_label=f"derived:{file_path.name}",
                )
            )
            slot += 1
            if frame is not None or len(sources) >= frame_limit:
                return sources
    return sources


def _evaluate_frame(
    source: FrameSource,
    raw_bundle: RawBundle | None,
    thresholds: list[float],
    lambda2_band: float,
    domain_override: float | None,
    warnings: list[str],
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "frame": int(source.slot),
        "snapshot": int(source.snapshot),
        "source_path": str(source.path),
        "source_type": source.source_label,
        "status": OK_STATUS,
    }
    row_thresholds: list[dict[str, Any]] = []

    try:
        lambda2, lambda2_source = _load_lambda2_from_derived(source.data, source.frame_arg)
        reconstructed = False
        reconstruction_meta = None
        if lambda2 is None:
            if raw_bundle is None:
                raise ValueError("missing lambda2 and no raw archive for reconstruction")
            u, v, w = _load_velocity_frame(raw_bundle, source.snapshot)
            lambda2 = _lambda2_from_velocity(u, v, w, raw_bundle.domain_length)
            lambda2_source = f"reconstructed_from_raw:{raw_bundle.path.name}"
            reconstructed = True
            reconstruction_meta = {
                "raw_path": str(raw_bundle.path),
                "raw_snapshot": int(source.snapshot),
                "raw_domain_length": float(raw_bundle.domain_length),
            }

        if lambda2 is None or np.asarray(lambda2).ndim != 3:
            raise ValueError(f"lambda2 must be 3D, got {None if lambda2 is None else np.asarray(lambda2).shape!r}")
        lambda2 = np.asarray(lambda2, dtype=np.float64)
        n = int(lambda2.shape[0])
        if int(lambda2.shape[1]) != n or int(lambda2.shape[2]) != n:
            raise ValueError(f"lambda2 must be cubic, got {lambda2.shape!r}")

        domain_length, domain_source = _resolve_domain_length(
            raw_bundle.data if raw_bundle is not None else None,
            source.data,
            domain_override,
            n,
            warnings,
        )
        row["domain_length"] = float(domain_length)
        row["domain_length_source"] = domain_source
        if domain_source.startswith("fallback"):
            row["status"] = DEGRADED_STATUS

        grad = _gradient_magnitude(lambda2, domain_length)
        finite = np.isfinite(lambda2) & np.isfinite(grad)
        cell_count = int(lambda2.size)
        finite_count = int(np.count_nonzero(finite))
        if finite_count == 0:
            row["status"] = ERROR_STATUS
            row["cell_count"] = cell_count
            row["finite_cell_count"] = 0
            row["errors"] = ["no finite lambda2 or gradient cells"]
            return row
        if finite_count != cell_count:
            row["status"] = DEGRADED_STATUS
            warnings.append(f"frame {source.slot}: dropping {cell_count - finite_count} non-finite cells")

        lambda2_f = lambda2[finite]
        grad_f = np.abs(grad)[finite]
        band_mask = np.abs(lambda2_f) <= float(lambda2_band)
        band_count = int(np.count_nonzero(band_mask))

        row["lambda2_source"] = lambda2_source
        row["lambda2_reconstructed"] = bool(reconstructed)
        if reconstruction_meta is not None:
            row["reconstruction_meta"] = reconstruction_meta
        row["cell_count"] = cell_count
        row["finite_cell_count"] = finite_count
        row["band_cell_count"] = band_count
        row["band_cell_fraction"] = float(band_count / float(finite_count)) if finite_count else 0.0
        row["lambda2_band"] = float(lambda2_band)
        row["grad_lambda2_stats"] = _stats(grad_f)

        band_grad = grad_f[band_mask]
        row["band_grad_count"] = int(band_count)
        row["band_grad_stats"] = _stats(band_grad)
        if band_count == 0:
            row["status"] = DEGRADED_STATUS
            row["grad_threshold_rows"] = [
                {"threshold": float(threshold), "count": 0, "fraction_band": 0.0, "fraction_domain": 0.0}
                for threshold in thresholds
            ]
            return row

        for threshold in thresholds:
            count = int(np.count_nonzero(band_grad >= float(threshold)))
            row_thresholds.append(
                {
                    "threshold": float(threshold),
                    "count": count,
                    "fraction_band": float(count / float(band_count)),
                    "fraction_domain": float(count / float(finite_count)),
                }
            )
        row["grad_threshold_rows"] = row_thresholds
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"{type(exc).__name__}:{exc}"]
    return row


def _collect_threshold_values(
    rows: list[dict[str, Any]],
    key: str,
    threshold: float,
) -> list[float]:
    values: list[float] = []
    for row in rows:
        items = row.get("grad_threshold_rows")
        if not isinstance(items, list):
            continue
        for item in items:
            if not isinstance(item, dict):
                continue
            t = item.get("threshold")
            if not isinstance(t, (int, float)):
                continue
            if not math.isclose(float(t), threshold, rel_tol=0.0, abs_tol=0.0):
                continue
            value = item.get(key)
            if isinstance(value, (int, float)) and math.isfinite(float(value)):
                values.append(float(value))
    return values


def _collect_float(values: list[float | int] | list[Any]) -> list[float]:
    return [float(value) for value in values if isinstance(value, (int, float)) and math.isfinite(float(value))]


def _build_summary(rows: list[dict[str, Any]], thresholds: list[float], requested_frame_limit: int) -> dict[str, Any]:
    status_counts = {
        OK_STATUS: 0,
        DEGRADED_STATUS: 0,
        MISSING_REQUIRED_STATUS: 0,
        ERROR_STATUS: 0,
    }
    for row in rows:
        status = row.get("status")
        if isinstance(status, str):
            status_counts[status] = status_counts.get(status, 0) + 1

    usable = [row for row in rows if row.get("status") in (OK_STATUS, DEGRADED_STATUS)]
    band_fractions = [row.get("band_cell_fraction") for row in usable if isinstance(row.get("band_cell_fraction"), (int, float))]
    grad_min = [row.get("grad_lambda2_stats", {}).get("min") for row in usable]
    grad_mean = [row.get("grad_lambda2_stats", {}).get("mean") for row in usable]
    grad_max = [row.get("grad_lambda2_stats", {}).get("max") for row in usable]
    band_grad_min = [row.get("band_grad_stats", {}).get("min") for row in usable]
    band_grad_mean = [row.get("band_grad_stats", {}).get("mean") for row in usable]
    band_grad_max = [row.get("band_grad_stats", {}).get("max") for row in usable]

    threshold_summary: dict[str, Any] = {}
    for threshold in thresholds:
        count_values = _collect_float(_collect_threshold_values(usable, "count", threshold))
        frac_band_values = _collect_float(_collect_threshold_values(usable, "fraction_band", threshold))
        frac_dom_values = _collect_float(_collect_threshold_values(usable, "fraction_domain", threshold))
        threshold_summary[str(threshold)] = {
            "count_stats": {
                "frame_count": int(len(count_values)),
                "min": min(count_values) if count_values else None,
                "mean": (sum(count_values) / len(count_values)) if count_values else None,
                "max": max(count_values) if count_values else None,
            },
            "fraction_band_stats": {
                "frame_count": int(len(frac_band_values)),
                "min": min(frac_band_values) if frac_band_values else None,
                "mean": (sum(frac_band_values) / len(frac_band_values)) if frac_band_values else None,
                "max": max(frac_band_values) if frac_band_values else None,
            },
            "fraction_domain_stats": {
                "frame_count": int(len(frac_dom_values)),
                "min": min(frac_dom_values) if frac_dom_values else None,
                "mean": (sum(frac_dom_values) / len(frac_dom_values)) if frac_dom_values else None,
                "max": max(frac_dom_values) if frac_dom_values else None,
            },
        }

    band_fractions_f = _collect_float(band_fractions)
    grad_min_f = _collect_float(grad_min)
    grad_mean_f = _collect_float(grad_mean)
    grad_max_f = _collect_float(grad_max)
    band_grad_min_f = _collect_float(band_grad_min)
    band_grad_mean_f = _collect_float(band_grad_mean)
    band_grad_max_f = _collect_float(band_grad_max)

    return {
        "requested_frame_limit": int(requested_frame_limit),
        "processed_frame_count": int(len(rows)),
        "ok_frame_count": int(status_counts.get(OK_STATUS, 0)),
        "degraded_frame_count": int(status_counts.get(DEGRADED_STATUS, 0)),
        "missing_frame_count": int(status_counts.get(MISSING_REQUIRED_STATUS, 0)),
        "error_frame_count": int(status_counts.get(ERROR_STATUS, 0)),
        "status_counts": {status: int(count) for status, count in status_counts.items() if count},
        "band_cell_fraction_stats": {
            "min": min(band_fractions_f) if band_fractions_f else None,
            "mean": (sum(band_fractions_f) / len(band_fractions_f)) if band_fractions_f else None,
            "max": max(band_fractions_f) if band_fractions_f else None,
        },
        "grad_lambda2_stats": {
            "min_of_min": min(grad_min_f) if grad_min_f else None,
            "mean_of_mean": (sum(grad_mean_f) / len(grad_mean_f)) if grad_mean_f else None,
            "max_of_max": max(grad_max_f) if grad_max_f else None,
            "sample_count": int(len(grad_min_f)),
        },
        "band_grad_stats": {
            "min_of_min": min(band_grad_min_f) if band_grad_min_f else None,
            "mean_of_mean": (sum(band_grad_mean_f) / len(band_grad_mean_f)) if band_grad_mean_f else None,
            "max_of_max": max(band_grad_max_f) if band_grad_max_f else None,
            "sample_count": int(len(band_grad_min_f)),
        },
        "threshold_summary": threshold_summary,
        "all_frames_ok_or_degraded": bool(all(row.get("status") in (OK_STATUS, DEGRADED_STATUS) for row in rows)),
    }


def _build_payload(args: argparse.Namespace) -> dict[str, Any]:
    thresholds = _coerce_thresholds(list(args.grad_threshold))
    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": OK_STATUS,
        "route_decision": ROUTE_DECISION,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        "script": SCRIPT_NAME,
        **CONTROL_CARD,
        "inputs": {
            "raw_archive": str(args.raw_archive) if args.raw_archive is not None else None,
            "derived_archive": str(args.derived_archive) if args.derived_archive is not None else None,
            "input_dir": str(args.input_dir),
            "frame": args.frame,
            "frame_limit": int(args.frame_limit),
            "lambda2_band": float(args.lambda2_band),
            "gradient_thresholds": thresholds,
            "domain_length_override": None if args.domain_length is None else float(args.domain_length),
        },
        "rows": [],
        "summary": {},
        "warnings": [],
        "errors": [],
    }

    if not thresholds:
        payload["status"] = ERROR_STATUS
        payload["errors"] = ["no valid gradient thresholds"]
        payload["summary"] = _build_summary([], thresholds, int(args.frame_limit))
        return payload

    raw_path = args.raw_archive
    derived_path = args.derived_archive
    if raw_path is None and args.input_dir.exists():
        try:
            raw_path = _find_candidate_npz(args.input_dir, "raw")
        except Exception:
            raw_path = None
    if derived_path is None and args.input_dir.exists():
        try:
            derived_path = _find_candidate_npz(args.input_dir, "derived")
        except Exception:
            derived_path = None

    payload["inputs"]["raw_archive"] = str(raw_path) if raw_path is not None else None
    payload["inputs"]["derived_archive"] = str(derived_path) if derived_path is not None else None

    warnings: list[str] = []
    raw_bundle: RawBundle | None = None
    if raw_path is not None:
        try:
            raw_bundle = _load_velocity_bundle(raw_path)
        except Exception as exc:
            payload["warnings"].append(f"raw_bundle_load_failed:{type(exc).__name__}:{exc}")
            raw_bundle = None
    else:
        payload["warnings"].append("raw_archive_not_provided")

    derived_sources: list[FrameSource] = []
    if derived_path is not None:
        try:
            derived_sources = _load_derived_sources(derived_path, int(args.frame_limit), args.frame)
        except Exception as exc:
            payload["warnings"].append(f"derived_source_load_failed:{type(exc).__name__}:{exc}")
            derived_sources = []

    sources: list[FrameSource] = []
    if derived_sources:
        sources = derived_sources
    elif raw_bundle is not None:
        if args.frame is not None:
            if args.frame >= raw_bundle.frame_count:
                payload["status"] = ERROR_STATUS
                payload["errors"] = [f"requested frame {args.frame} out of raw range {raw_bundle.frame_count}"]
                payload["summary"] = _build_summary([], thresholds, int(args.frame_limit))
                payload["warnings"] = sorted(set(payload["warnings"] + warnings))
                return payload
            requested = [args.frame]
        else:
            requested = list(range(min(int(args.frame_limit), raw_bundle.frame_count)))
        for frame in requested:
            sources.append(
                FrameSource(
                    slot=int(frame),
                    snapshot=int(frame),
                    data=raw_bundle.data,
                    path=raw_bundle.path,
                    frame_arg=int(frame),
                    source_label="raw_reconstruction",
                )
            )

    if not sources:
        payload["status"] = MISSING_REQUIRED_STATUS
        payload["errors"] = ["no usable derived lambda2 and no raw reconstruction source"]
        payload["summary"] = _build_summary([], thresholds, int(args.frame_limit))
        payload["warnings"] = sorted(set(payload["warnings"] + warnings))
        return payload

    rows: list[dict[str, Any]] = []
    for source in sources:
        rows.append(_evaluate_frame(source, raw_bundle, thresholds, float(args.lambda2_band), args.domain_length, warnings))

    payload["rows"] = rows
    payload["summary"] = _build_summary(rows, thresholds, int(args.frame_limit))
    payload["warnings"] = sorted(set(payload["warnings"] + warnings))
    if any(row.get("status") == ERROR_STATUS for row in rows):
        payload["status"] = ERROR_STATUS
    elif any(row.get("status") == MISSING_REQUIRED_STATUS for row in rows):
        payload["status"] = MISSING_REQUIRED_STATUS
    elif any(row.get("status") == DEGRADED_STATUS for row in rows):
        payload["status"] = DEGRADED_STATUS
    else:
        payload["status"] = OK_STATUS

    if payload["status"] in (MISSING_REQUIRED_STATUS, ERROR_STATUS) and not payload["errors"]:
        payload["errors"] = [f"scan ended with status {payload['status']}"]
    return payload


def main() -> int:
    args = _parse_args()
    payload = _build_payload(args)
    output = _json_text(payload, pretty=args.pretty) + "\n"
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(output, encoding="utf-8")
    if args.json:
        print(output, end="")
    return 0 if payload.get("status") in (OK_STATUS, DEGRADED_STATUS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
