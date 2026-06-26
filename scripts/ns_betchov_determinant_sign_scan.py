#!/usr/bin/env python3
"""Scan corrected Betchov sign relation between lambda2 and det(S) on the N128 archive."""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_betchov_determinant_sign_scan.py"
CONTRACT = "ns_betchov_determinant_sign_scan"
ROUTE_DECISION = "FAIL_CLOSED_BETCHOV_DETERMINANT_SIGN_SCAN"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
LEGACY_AXIS_WARNING_SUFFIXES = (
    "velocity_snapshots detected as legacy (T,N,N,N,3)",
    "5D velocity layout interpreted as (T,N,N,N,3)",
)

DEFAULT_DERIVED_ARCHIVE = DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_betchov_determinant_sign_scan_N128_20260620.json"
)

DEFAULT_ZERO_EPS = 1.0e-12

LAMBDA2_KEYS = ("lambda2",)
DET_KEYS = (
    "detS",
    "detS_field",
    "det_strain",
    "det_of_strain",
    "strain_determinant",
    "determinant",
    "determinant_of_strain",
)


CONTROL_CARD = {
    "O": "Measure the corrected Betchov determinant gate on the available N128 archive.",
    "R": "Per-frame and aggregate counts/fractions for sign bins of lambda2 and det(S), mismatch counts, and minima/maxima.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical scan: if required inputs are unavailable the scan is marked partial/missing, never promoting conclusions.",
    "L": "Load derived NPZ frames (or a single archive), optional raw archive reconstruction, then emit per-frame and aggregate stats.",
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion authority is inferred by this script.",
    "F": "If lambda2 or det(S) are unavailable in derived data and cannot be reconstructed from raw velocity, output degrades with explicit missing status/warnings.",
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


def _coerce_float(value: Any, *, finite: bool = True, name: str | None = None) -> float:
    parsed = float(value)
    if finite and not math.isfinite(parsed):
        raise ValueError(f"{name or 'value'} must be finite")
    return parsed


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


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _find_field(data: dict[str, np.ndarray], aliases: tuple[str, ...]) -> tuple[str | None, np.ndarray | None]:
    for alias in aliases:
        if alias in data:
            return alias, np.asarray(data[alias])

    normalized = {_normalize_key(alias): alias for alias in aliases}
    for key, value in data.items():
        if isinstance(key, str) and _normalize_key(key) in normalized:
            return key, np.asarray(value)
    return None, None


def _load_npz(path: Path) -> dict[str, np.ndarray]:
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
                    "grid_spacing",
                    "dx",
                    "domain_length",
                    "length",
                    "L",
                    "domain",
                    "N",
                    "N1",
                    "N2",
                    "N3",
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


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _is_benign_warning(warning: str) -> bool:
    if not isinstance(warning, str):
        return False
    return any(suffix in warning for suffix in LEGACY_AXIS_WARNING_SUFFIXES)


def _sign_counts(values: np.ndarray, eps: float) -> tuple[int, int, int]:
    pos = int(np.count_nonzero(values > eps))
    neg = int(np.count_nonzero(values < -eps))
    zero = int(values.size - pos - neg)
    return pos, neg, zero


def _minmax_with_location(values: np.ndarray, mask: np.ndarray) -> tuple[float, float, list[int], list[int]]:
    valid = np.where(mask, values, np.nan)
    finite_count = int(np.count_nonzero(np.isfinite(valid)))
    if finite_count <= 0:
        raise ValueError("no finite cells in masked array")
    arg_min = int(np.argmin(np.where(mask, values, np.inf)))
    arg_max = int(np.argmax(np.where(mask, values, -np.inf)))
    return (
        float(np.nanmin(valid)),
        float(np.nanmax(valid)),
        list(map(int, np.unravel_index(arg_min, values.shape))),
        list(map(int, np.unravel_index(arg_max, values.shape))),
    )


def _load_derived_frames(path: Path) -> list[tuple[int, int, dict[str, np.ndarray], Path]]:
    if not path.exists():
        raise FileNotFoundError(f"derived archive missing: {path}")

    archive_paths: list[Path]
    if path.is_file():
        archive_paths = [path]
    elif path.is_dir():
        archive_paths = sorted((entry for entry in path.iterdir() if entry.suffix.lower() == ".npz"), key=_frame_sort_key)
        if not archive_paths:
            raise FileNotFoundError(f"derived archive directory has no .npz files: {path}")
    else:
        raise ValueError(f"derived archive must be directory or npz path: {path}")

    frames: list[tuple[int, int, dict[str, np.ndarray], Path]] = []
    frame_slot = 0

    for archive_path in archive_paths:
        data = _load_npz(archive_path)
        _, lambda2_raw = _find_field(data, LAMBDA2_KEYS)
        _, det_raw = _find_field(data, DET_KEYS)

        frame_count = 1
        if lambda2_raw is not None and lambda2_raw.ndim == 4:
            frame_count = int(lambda2_raw.shape[0])
        elif det_raw is not None and det_raw.ndim == 4:
            frame_count = int(det_raw.shape[0])
        elif "velocity_snapshots" in data:
            velocity = np.asarray(data["velocity_snapshots"])
            if velocity.ndim == 5 and velocity.shape[-1] == 3:
                frame_count = int(velocity.shape[0])
            elif velocity.ndim == 4 and velocity.shape[-1] == 3:
                frame_count = 1

        snapshot_values = None
        if "snapshot_index" in data:
            snap = np.asarray(data["snapshot_index"])
            if snap.shape == ():
                snapshot_values = np.asarray([int(snap.item())], dtype=np.int64)
            elif snap.ndim == 1 and snap.size > 0:
                snapshot_values = snap.astype(np.int64, copy=False)

        for local_frame in range(frame_count):
            frame_data: dict[str, np.ndarray] = {}
            for key, value in data.items():
                arr = np.asarray(value)
                if arr.ndim == 4 and int(arr.shape[0]) == frame_count:
                    frame_data[key] = arr[local_frame]
                else:
                    frame_data[key] = arr

            snapshot_id = local_frame
            if snapshot_values is not None and len(snapshot_values) > local_frame:
                snapshot_id = int(snapshot_values[local_frame])

            frames.append((frame_slot, snapshot_id, frame_data, archive_path))
            frame_slot += 1

    return frames


def _coerce_path(value: Any) -> Path | None:
    if value is None:
        return None
    if isinstance(value, bytes):
        text = value.decode("utf-8", errors="ignore")
    else:
        if isinstance(value, np.ndarray):
            array = np.asarray(value)
            if array.shape == ():
                text = str(array.item())
            elif array.ndim == 1 and array.size == 1:
                text = str(array.reshape(-1)[0].item())
            else:
                text = str(array)
        else:
            text = str(value)
    text = text.strip()
    if not text or text.lower() == "none":
        return None
    candidate = Path(text)
    return candidate if candidate.exists() else None


def _infer_raw_candidates(derived_archive: Path, frames: list[tuple[int, int, dict[str, np.ndarray], Path]], explicit: Path | None) -> list[Path]:
    candidates: list[Path] = []
    if explicit is not None:
        explicit = explicit.expanduser()
        if explicit.exists():
            candidates.append(explicit)

    for _, _, frame_data, _ in frames:
        for key in (
            "input_path",
            "source_path",
            "raw_archive",
            "raw_path",
            "input",
            "velocity_archive",
            "pressure_archive",
        ):
            if key not in frame_data:
                continue
            candidate = _coerce_path(frame_data[key])
            if candidate is not None and candidate not in candidates:
                candidates.append(candidate)

    fallback = DEFAULT_RAW_ARCHIVE
    if fallback.exists() and fallback not in candidates:
        candidates.append(fallback)

    fallback_dir = derived_archive.parent / "ns3d_N128_seed0_gpu_pressure.npz"
    if fallback_dir.exists() and fallback_dir not in candidates:
        candidates.append(fallback_dir)

    return candidates


@dataclass(frozen=True)
class RawBundle:
    path: Path
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    has_frame_axis: bool
    frame_count: int
    domain_length: float


def _select_velocity_components(data: dict[str, np.ndarray], warnings: list[str]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if "velocity_snapshots" in data:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        if velocity.ndim == 5 and velocity.shape[1] == 3 and velocity.shape[-1] != 3:
            warnings.append("velocity_snapshots detected on axis 1 as component axis")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots detected as legacy (T,N,N,N,3)")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        if velocity.ndim == 4 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots detected on last axis")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(
            f"velocity_snapshots has unsupported shape {velocity.shape!r}; expected (T,N,N,N,3) or (N,N,N,3)"
        )

    if "u" in data and "v" in data and "w" in data:
        u = np.asarray(data["u"], dtype=np.float64)
        v = np.asarray(data["v"], dtype=np.float64)
        w = np.asarray(data["w"], dtype=np.float64)
        return u, v, w

    if "velocity" in data and isinstance(data["velocity"], np.ndarray):
        velocity = np.asarray(data["velocity"], dtype=np.float64)
        if velocity.ndim == 4 and velocity.shape[1] == 3:
            warnings.append("velocity channels detected on axis 1 in fallback key 'velocity'")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity channels detected on last axis in fallback key 'velocity'")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"velocity fallback key has unsupported shape {velocity.shape!r}")

    raise ValueError("raw archive missing velocity payload")


def _infer_domain_length(data: dict[str, np.ndarray], n: int, warnings: list[str]) -> float:
    domain_length, domain_key = _read_scalar_metadata(data, ("domain_length", "length", "L", "domain"))
    if domain_length is not None:
        domain_length_f = _coerce_float(domain_length, name=domain_key or "domain_length")
        if domain_length_f <= 0:
            raise ValueError("domain_length must be positive")
    else:
        domain_length_f = None

    grid_spacing, spacing_key = _read_scalar_metadata(data, ("grid_spacing", "dx", "dh"))
    if grid_spacing is not None:
        spacing_f = _coerce_float(grid_spacing, name=spacing_key or "grid_spacing")
        if spacing_f <= 0:
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
    warnings.append(f"domain_length unavailable; falling back to {fallback}")
    return fallback


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
        # Legacy frame-first layout with trailing vector channel.
        if int(u.shape[-1]) != 3:
            raise ValueError(f"unsupported 5D velocity shape {u.shape!r}")
        warnings.append("5D velocity layout interpreted as (T,N,N,N,3)")
        u = u[..., 0]
        v = v[..., 1]
        w = w[..., 2]
        has_frame_axis = True
        frame_count = int(u.shape[0])
        if u.ndim != 4:
            raise ValueError(f"unexpected post-extract velocity rank {u.ndim}")
    else:
        raise ValueError(f"unsupported velocity component shape {u.shape!r} (u,v,w ranks must agree)")

    if has_frame_axis:
        # u/v/w are (T, N, N, N).
        n = int(u.shape[1])
    else:
        # u/v/w are (N, N, N).
        n = int(u.shape[-1])
    if n <= 1:
        raise ValueError(f"invalid grid size n={n}")
    if has_frame_axis:
        if u.shape[1] != u.shape[2] or u.shape[2] != u.shape[3]:
            raise ValueError(f"velocity snapshot shape not cubic: {u.shape!r}")
        if u.shape[1] != n:
            raise ValueError(f"velocity grid mismatch: {u.shape!r}")
    else:
        if u.shape[0] != u.shape[1] or u.shape[1] != u.shape[2]:
            raise ValueError(f"velocity component shape not cubic: {u.shape!r}")

    if not np.all(np.isfinite(u)) or not np.all(np.isfinite(v)) or not np.all(np.isfinite(w)):
        warnings.append(f"raw_velocity_has_nans_in_{path.name}")
        raise ValueError(f"raw velocity contains non-finite values in {path}")

    domain_length = _infer_domain_length(data, n, warnings)
    return RawBundle(path=path, u=u, v=v, w=w, has_frame_axis=has_frame_axis, frame_count=frame_count, domain_length=domain_length)


def _raw_velocity_frame(bundle: RawBundle, snapshot: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if not bundle.has_frame_axis:
        if snapshot != 0:
            raise ValueError(f"raw archive has no frame axis; requested snapshot {snapshot}")
        u = np.asarray(bundle.u, dtype=np.float64)
        v = np.asarray(bundle.v, dtype=np.float64)
        w = np.asarray(bundle.w, dtype=np.float64)
        if u.ndim != 3:
            raise ValueError(f"raw component without frame axis must be 3D, got {u.shape!r}")
        return u, v, w

    frame_count = int(bundle.frame_count)
    if snapshot < 0 or snapshot >= frame_count:
        raise ValueError(f"raw snapshot {snapshot} out of range for {frame_count}")
    u = np.asarray(bundle.u, dtype=np.float64)[snapshot]
    v = np.asarray(bundle.v, dtype=np.float64)[snapshot]
    w = np.asarray(bundle.w, dtype=np.float64)[snapshot]
    if u.ndim != 3:
        raise ValueError(f"raw snapshot components must be 3D, got {u.shape!r}")
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


def _determinant_from_velocity(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    u = np.asarray(u, dtype=np.float64)
    v = np.asarray(v, dtype=np.float64)
    w = np.asarray(w, dtype=np.float64)
    if not (u.shape == v.shape == w.shape):
        raise ValueError("velocity component shapes must agree")
    if u.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {u.shape!r}")
    if int(u.shape[0]) <= 1:
        raise ValueError("velocity grid must have n>1")
    if not math.isfinite(float(domain_length)) or float(domain_length) <= 0.0:
        raise ValueError("domain_length must be finite positive")

    n = int(u.shape[0])
    if int(u.shape[1]) != n or int(u.shape[2]) != n:
        raise ValueError(f"velocity components must be cubic, got {u.shape!r}")

    k = 2.0 * math.pi * np.fft.fftfreq(n, d=domain_length / float(n))
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

    det_s = (
        s11 * (s22 * s33 - s23 * s23)
        - s12 * (s12 * s33 - s23 * s13)
        + s13 * (s12 * s23 - s22 * s13)
    )
    return np.asarray(det_s, dtype=np.float64)


def _lambda2_and_det_from_velocity(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray]:
    u = np.asarray(u, dtype=np.float64)
    v = np.asarray(v, dtype=np.float64)
    w = np.asarray(w, dtype=np.float64)
    if not (u.shape == v.shape == w.shape):
        raise ValueError("velocity component shapes must agree")
    if u.ndim != 3:
        raise ValueError(f"velocity components must be 3D, got {u.shape!r}")
    if int(u.shape[0]) <= 1:
        raise ValueError("velocity grid must have n>1")
    if not math.isfinite(float(domain_length)) or float(domain_length) <= 0.0:
        raise ValueError("domain_length must be finite positive")

    n = int(u.shape[0])
    if int(u.shape[1]) != n or int(u.shape[2]) != n:
        raise ValueError(f"velocity components must be cubic, got {u.shape!r}")

    k = 2.0 * math.pi * np.fft.fftfreq(n, d=domain_length / float(n))
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

    eigenvalues = np.linalg.eigvalsh(strain)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    det_s = np.asarray(np.linalg.det(strain), dtype=np.float64)
    return lambda2, det_s


def _select_cubic_field(value: np.ndarray, field_name: str, *, strict: bool = False) -> np.ndarray:
    arr = np.asarray(value)
    if arr.ndim == 4:
        if arr.shape[0] != 1:
            raise ValueError(f"{field_name} is a frame stack with unresolved frame axis, got {arr.shape!r}")
        arr = arr[0]
    if arr.ndim != 3:
        raise ValueError(f"{field_name} must be 3D after frame extraction, got {arr.shape!r}")
    if strict and not np.all(np.isfinite(arr)):
        raise ValueError(f"{field_name} contains non-finite values")
    n = int(arr.shape[0])
    if int(arr.shape[1]) != n or int(arr.shape[2]) != n:
        raise ValueError(f"{field_name} must be cubic, got {arr.shape!r}")
    return np.asarray(arr, dtype=np.float64)


def _evaluate_frame(
    slot: int,
    snapshot: int,
    frame_data: dict[str, np.ndarray],
    source: Path,
    raw_bundle: RawBundle | None,
    eps: float,
    warnings: list[str],
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(source),
        "expected_relation": "sign(lambda2) * sign(det(S)) <= 0",
    }

    lambda2_key, lambda2_raw = _find_field(frame_data, LAMBDA2_KEYS)
    lambda2: np.ndarray | None = None
    lambda2_source: str | None = None
    if lambda2_raw is not None:
        lambda2 = _select_cubic_field(np.asarray(lambda2_raw), lambda2_key or "lambda2")
        lambda2_source = f"derived:{lambda2_key or 'lambda2'}"

    det_key, det_raw = _find_field(frame_data, DET_KEYS)
    det: np.ndarray | None = None
    det_source: str | None = None

    if det_raw is not None:
        det = _select_cubic_field(np.asarray(det_raw), det_key or "detS")
        det_source = f"derived:{det_key or 'detS'}"
    elif raw_bundle is not None:
        try:
            u, v, w = _raw_velocity_frame(raw_bundle, snapshot)
            raw_lambda2, raw_det = _lambda2_and_det_from_velocity(u, v, w, raw_bundle.domain_length)
            if lambda2 is None:
                lambda2 = raw_lambda2
                lambda2_source = f"raw:{raw_bundle.path.name}#snapshot={snapshot}"
            det = raw_det
            det_source = f"raw:{raw_bundle.path.name}#snapshot={snapshot}"
        except Exception as exc:
            row["status"] = ERROR_STATUS
            row["errors"] = [f"lambda2/det(S) reconstruction failure: {exc}"]
            row["notes"] = ["raw archive present but lambda2/det(S) reconstruction failed"]
            return ERROR_STATUS, row

    if lambda2 is None:
        row["status"] = MISSING_REQUIRED_STATUS
        row["errors"] = ["lambda2 missing and no usable raw velocity archive available"]
        return MISSING_REQUIRED_STATUS, row

    if det is None:
        row["status"] = MISSING_REQUIRED_STATUS
        row["errors"] = ["detS missing and no usable raw velocity archive available"]
        return MISSING_REQUIRED_STATUS, row

    if det.shape != lambda2.shape:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"shape mismatch: lambda2={lambda2.shape!r}, detS={det.shape!r}"]
        return ERROR_STATUS, row

    finite = np.isfinite(lambda2) & np.isfinite(det)
    cell_count = int(lambda2.size)
    valid_count = int(np.count_nonzero(finite))
    if valid_count == 0:
        row["status"] = ERROR_STATUS
        row["cell_count"] = cell_count
        row["errors"] = ["no finite pair (lambda2, detS) cells"]
        row["det_source"] = det_source
        row["lambda2_source"] = lambda2_source or (lambda2_key or "lambda2")
        return ERROR_STATUS, row

    if valid_count != cell_count:
        warnings.append(f"frame {slot}: excluding {cell_count - valid_count} non-finite cells from sign statistics")

    l2 = lambda2[finite]
    d = det[finite]

    l2_pos, l2_neg, l2_zero = _sign_counts(l2, eps)
    d_pos, d_neg, d_zero = _sign_counts(d, eps)
    mismatch_count = int(np.count_nonzero(
        ((l2 > eps) & (d > eps)) | ((l2 < -eps) & (d < -eps))
    ))

    l2_min, l2_max, l2_argmin, l2_argmax = _minmax_with_location(lambda2, finite)
    d_min, d_max, d_argmin, d_argmax = _minmax_with_location(det, finite)

    row.update(
        {
            "status": OK_STATUS,
            "lambda2_source": lambda2_source or (lambda2_key or "lambda2"),
            "det_source": det_source,
            "cell_count": cell_count,
            "valid_cell_count": valid_count,
            "lambda2_positive_count": l2_pos,
            "lambda2_negative_count": l2_neg,
            "lambda2_zero_count": l2_zero,
            "lambda2_positive_fraction": _fraction(l2_pos, valid_count),
            "lambda2_negative_fraction": _fraction(l2_neg, valid_count),
            "lambda2_zero_fraction": _fraction(l2_zero, valid_count),
            "det_positive_count": d_pos,
            "det_negative_count": d_neg,
            "det_zero_count": d_zero,
            "det_positive_fraction": _fraction(d_pos, valid_count),
            "det_negative_fraction": _fraction(d_neg, valid_count),
            "det_zero_fraction": _fraction(d_zero, valid_count),
            "mismatch_count": mismatch_count,
            "mismatch_fraction": _fraction(mismatch_count, valid_count),
            "lambda2_min": l2_min,
            "lambda2_max": l2_max,
            "lambda2_argmin": l2_argmin,
            "lambda2_argmax": l2_argmax,
            "det_min": d_min,
            "det_max": d_max,
            "det_argmin": d_argmin,
            "det_argmax": d_argmax,
        }
    )
    return OK_STATUS, row


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
        "global_mismatch_count": 0,
        "global_sign_success_count": 0,
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

        for key in (
            "lambda2_positive_count",
            "lambda2_negative_count",
            "lambda2_zero_count",
            "det_positive_count",
            "det_negative_count",
            "det_zero_count",
            "mismatch_count",
        ):
            aggregate_key = "global_" + key if not key.startswith("global_") else key
            aggregate[aggregate_key] += int(row.get(key, 0))

        for frame_key, value_key, label in (
            ("global_lambda2_min", "lambda2_min", "lambda2_min"),
            ("global_lambda2_max", "lambda2_max", "lambda2_max"),
            ("global_det_min", "det_min", "det_min"),
            ("global_det_max", "det_max", "det_max"),
        ):
            value = row.get(value_key)
            if value is None:
                continue
            value_f = float(value)
            if aggregate[frame_key] is None or (
                frame_key.endswith("_min") and value_f < float(aggregate[frame_key])
            ) or (frame_key.endswith("_max") and value_f > float(aggregate[frame_key])):
                aggregate[frame_key] = value_f
                if frame_key == "global_lambda2_min":
                    aggregate["global_lambda2_min_frame"] = {
                        "frame": row.get("frame"),
                        "snapshot_index": row.get("snapshot_index"),
                        "index": row.get("lambda2_argmin"),
                    }
                if frame_key == "global_lambda2_max":
                    aggregate["global_lambda2_max_frame"] = {
                        "frame": row.get("frame"),
                        "snapshot_index": row.get("snapshot_index"),
                        "index": row.get("lambda2_argmax"),
                    }
                if frame_key == "global_det_min":
                    aggregate["global_det_min_frame"] = {
                        "frame": row.get("frame"),
                        "snapshot_index": row.get("snapshot_index"),
                        "index": row.get("det_argmin"),
                    }
                if frame_key == "global_det_max":
                    aggregate["global_det_max_frame"] = {
                        "frame": row.get("frame"),
                        "snapshot_index": row.get("snapshot_index"),
                        "index": row.get("det_argmax"),
                    }

    v = int(aggregate["global_valid_cell_count"])
    aggregate["global_sign_success_count"] = max(v - int(aggregate["global_mismatch_count"]), 0)
    aggregate["global_sign_success_fraction"] = _fraction(aggregate["global_sign_success_count"], v)
    aggregate["global_lambda2_positive_fraction"] = _fraction(aggregate["global_lambda2_positive_count"], v)
    aggregate["global_lambda2_negative_fraction"] = _fraction(aggregate["global_lambda2_negative_count"], v)
    aggregate["global_lambda2_zero_fraction"] = _fraction(aggregate["global_lambda2_zero_count"], v)
    aggregate["global_det_positive_fraction"] = _fraction(aggregate["global_det_positive_count"], v)
    aggregate["global_det_negative_fraction"] = _fraction(aggregate["global_det_negative_count"], v)
    aggregate["global_det_zero_fraction"] = _fraction(aggregate["global_det_zero_count"], v)
    aggregate["global_mismatch_fraction"] = _fraction(aggregate["global_mismatch_count"], v)

    return aggregate


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--derived-archive", type=Path, default=DEFAULT_DERIVED_ARCHIVE, help="Derived archive file or directory")
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Optional raw archive path for reconstructing lambda2 and det(S)")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Analyze a single derived frame slot")
    parser.add_argument("--frame-limit", type=_positive_int, default=None, help="Limit total frames from start")
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS, help="Sign-threshold epsilon")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    if args.zero_eps < 0:
        raise ValueError("--zero-eps must be nonnegative")

    errors: list[str] = []
    warnings: list[str] = []
    raw_auto_detected = False

    try:
        derived_frames = _load_derived_frames(args.derived_archive)
    except Exception as exc:
        warnings.append(f"derived_archive:{exc}")
        derived_frames = []

    if args.frame_limit is not None:
        derived_frames = derived_frames[: args.frame_limit]

    if args.frame is not None:
        derived_frames = [entry for entry in derived_frames if entry[0] == args.frame]
        if not derived_frames and args.raw_archive is None:
            errors.append(f"frame {args.frame} not found in derived selection")

    raw_bundle: RawBundle | None = None
    raw_archive_path: Path | None = None
    for candidate in _infer_raw_candidates(args.derived_archive, derived_frames, args.raw_archive):
        try:
            warnings_from_raw: list[str] = []
            raw_bundle = _load_raw_bundle(candidate, warnings_from_raw)
            raw_archive_path = candidate
            raw_auto_detected = args.raw_archive is None and candidate != DEFAULT_RAW_ARCHIVE
            warnings.extend(warnings_from_raw)
            break
        except Exception:
            warnings.append(f"raw_candidate:{candidate}:unusable_for_velocity")
            raw_bundle = None
            raw_archive_path = None

    if raw_bundle is None and (args.raw_archive is not None or args.derived_archive is not None):
        warnings.append("no usable raw archive found for det(S) reconstruction")

    if not derived_frames and raw_bundle is not None:
        if args.frame is None:
            frame_ids = list(range(raw_bundle.frame_count))
        elif args.frame < raw_bundle.frame_count:
            frame_ids = [args.frame]
        else:
            errors.append(f"frame {args.frame} out of range for raw archive with {raw_bundle.frame_count} frames")
            frame_ids = []
        if args.frame_limit is not None:
            frame_ids = frame_ids[: args.frame_limit]
        derived_frames = [
            (frame_id, frame_id, {}, raw_bundle.path)
            for frame_id in frame_ids
        ]

    rows: list[dict[str, Any]] = []
    frame_statuses: list[str] = []

    for slot, snapshot_id, frame_data, source in derived_frames:
        try:
            status, row = _evaluate_frame(
                slot=slot,
                snapshot=snapshot_id,
                frame_data=frame_data,
                source=source,
                raw_bundle=raw_bundle,
                eps=float(args.zero_eps),
                warnings=warnings,
            )
        except Exception as exc:  # defensive: never abort the whole scan
            status = ERROR_STATUS
            row = {
                "frame": int(slot),
                "snapshot_index": int(snapshot_id),
                "source": str(source),
                "status": ERROR_STATUS,
                "errors": [f"frame_evaluation_error:{exc}"],
            }
        frame_statuses.append(str(status))
        rows.append(row)

    aggregate = _build_aggregate(rows)
    if not rows:
        status = MISSING_REQUIRED_STATUS
    elif any(status == ERROR_STATUS for status in frame_statuses):
        status = ERROR_STATUS
    elif any(status == MISSING_REQUIRED_STATUS for status in frame_statuses):
        status = PARTIAL_STATUS
    elif any(not _is_benign_warning(warning) for warning in warnings):
        status = PARTIAL_STATUS
    else:
        status = OK_STATUS
    if errors:
        status = ERROR_STATUS

    changed_files = [str(args.output)]

    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        **CONTROL_CARD,
        "inputs": {
            "derived_archive": str(args.derived_archive),
            "raw_archive": str(raw_archive_path) if raw_archive_path is not None else None,
            "raw_archive_auto_detected": raw_auto_detected,
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
        },
        "frames": rows,
        "aggregate": aggregate,
        "errors": errors,
        "warnings": warnings,
        "changed_files": changed_files,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
