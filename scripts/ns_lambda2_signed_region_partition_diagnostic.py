#!/usr/bin/env python3
"""Partition omega_norm_sq by signed lambda2 regions for NS archive pairs.

The diagnostic reads a raw archive with vorticity magnitude-squared data and a
derived per-frame directory containing ``lambda2`` arrays. For each aligned
frame it computes the fraction of total domain ``omega_norm_sq`` lying in the
requested signed lambda2 regions, then emits deterministic fail-closed JSON.
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


SCRIPT_NAME = "scripts/ns_lambda2_signed_region_partition_diagnostic.py"
CONTRACT = "ns_lambda2_signed_region_partition_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_LAMBDA2_SIGNED_REGION_PARTITION_DIAGNOSTIC"
OK_STATUS = "ok"
ERROR_STATUS = "error"
DEFAULT_FRAME_LIMIT = 13
DEFAULT_OUTPUT = Path("outputs/ns_lambda2_signed_region_partition_diagnostic.json")
DEFAULT_DOMAIN_LENGTH = 2.0 * math.pi

OMEGA_COMPONENT_SETS = (
    ("omega_x", "omega_y", "omega_z"),
    ("omega1", "omega2", "omega3"),
    ("w_x", "w_y", "w_z"),
    ("wx", "wy", "wz"),
    ("vorticity_x", "vorticity_y", "vorticity_z"),
    ("vorticity1", "vorticity2", "vorticity3"),
)

REGION_SPECS: tuple[tuple[str, str], ...] = (
    ("lambda2_lt_-10", "lambda2 < -10"),
    ("lambda2_-10_to_-3", "-10 <= lambda2 < -3"),
    ("lambda2_-3_to_-1", "-3 <= lambda2 < -1"),
    ("lambda2_-1_to_-0.1", "-1 <= lambda2 < -0.1"),
    ("lambda2_-0.1_to_0.1", "-0.1 <= lambda2 <= 0.1"),
    ("lambda2_0.1_to_1", "0.1 < lambda2 <= 1"),
    ("lambda2_1_to_3", "1 < lambda2 <= 3"),
    ("lambda2_3_to_10", "3 < lambda2 <= 10"),
    ("lambda2_gt_10", "lambda2 > 10"),
    ("lambda2_negative_total", "lambda2 < 0"),
    ("lambda2_near_zero_total", "|lambda2| <= 0.1"),
    ("lambda2_positive_total", "lambda2 > 0"),
)
PARTITION_REGION_NAMES = {
    "lambda2_lt_-10",
    "lambda2_-10_to_-3",
    "lambda2_-3_to_-1",
    "lambda2_-1_to_-0.1",
    "lambda2_-0.1_to_0.1",
    "lambda2_0.1_to_1",
    "lambda2_1_to_3",
    "lambda2_3_to_10",
    "lambda2_gt_10",
}


@dataclass(frozen=True)
class ArchiveBundle:
    path: Path
    data: dict[str, np.ndarray]
    frame_count: int


@dataclass(frozen=True)
class DerivedFrameSource:
    frame: int
    path: Path
    data: dict[str, np.ndarray]


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
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
        except Exception as exc:  # pragma: no cover - defensive path.
            raise ValueError(f"meta_json could not be parsed as JSON: {exc}") from exc
        if isinstance(meta, dict):
            for key in ("domain_length", "grid_spacing", "length", "N"):
                if key in meta and key not in payload:
                    payload[key] = np.asarray(meta[key])
    return payload


def _scalar_metadata(data: dict[str, np.ndarray], *names: str) -> tuple[Any | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape == ():
            scalar = value.item()
            if isinstance(scalar, bytes):
                scalar = scalar.decode("utf-8")
            if isinstance(scalar, np.generic):
                scalar = scalar.item()
            return scalar, name
        if value.ndim == 1 and value.size == 1:
            scalar = value.reshape(()).item()
            if isinstance(scalar, np.generic):
                scalar = scalar.item()
            return scalar, name
    return None, None


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return float(parsed)


def _load_frame_field(name: str, value: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(value, dtype=np.float64)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) != 1:
                raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frame")
            arr = arr[0]
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be 3D or single-snapshot 4D, got {arr.shape!r}")
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} contains non-finite values")
    return arr


def _extract_frame_count(data: dict[str, np.ndarray]) -> int:
    counts: set[int] = set()
    saw_3d = False
    for name in ("omega_norm_sq", "omega_snapshots", "omega_x", "omega_y", "omega_z", "omega1", "omega2", "omega3", "w_x", "w_y", "w_z", "wx", "wy", "wz", "vorticity_x", "vorticity_y", "vorticity_z", "vorticity1", "vorticity2", "vorticity3", "u", "v", "w", "u_hat", "v_hat", "w_hat"):
        if name not in data:
            continue
        arr = np.asarray(data[name])
        if arr.ndim == 4:
            counts.add(int(arr.shape[0]))
        elif arr.ndim == 5:
            counts.add(int(arr.shape[0]))
        elif arr.ndim == 3:
            saw_3d = True
        elif arr.shape == () or arr.ndim == 1:
            continue
        else:
            raise ValueError(f"{name} has unsupported rank {arr.ndim}")
    if counts and saw_3d:
        raise ValueError("mixed 3D and multi-frame fields are not supported in one archive")
    if len(counts) > 1:
        raise ValueError(f"frame counts do not match: {sorted(counts)!r}")
    if counts:
        return counts.pop()
    if saw_3d:
        return 1
    raise ValueError("archive does not contain any usable frame fields")


def _candidate_score(path: Path) -> tuple[int, str]:
    stem = path.stem.lower()
    score = 0
    if "frame" in stem:
        score += 2
    if "lambda2" in stem:
        score += 3
    if "derived" in stem or "tensor" in stem:
        score += 1
    return score, path.name


def _frame_sort_key(path: Path) -> tuple[int, str]:
    match = re.search(r"(?:^|[_-])frame[_-]?(\d+)(?:$|[_-])", path.stem)
    if match is not None:
        return int(match.group(1)), path.name
    return 10**12, path.name


def _find_npz_candidates(directory: Path) -> list[Path]:
    if not directory.exists():
        raise FileNotFoundError(f"derived archive directory not found: {directory}")
    if not directory.is_dir():
        raise ValueError(f"derived archive must be a directory, got {directory}")
    candidates = [path for path in directory.rglob("*.npz") if path.is_file()]
    if not candidates:
        raise FileNotFoundError(f"no .npz archives found under {directory}")
    return candidates


def _load_bundle(path: Path) -> ArchiveBundle:
    if not path.exists():
        raise FileNotFoundError(f"raw archive not found: {path}")
    if path.suffix.lower() != ".npz":
        raise ValueError(f"raw archive must be a .npz file, got {path}")
    data = _load_npz(path)
    return ArchiveBundle(path=path, data=data, frame_count=_extract_frame_count(data))


def _load_derived_sources(path: Path, frame_limit: int) -> list[DerivedFrameSource]:
    candidates = sorted(_find_npz_candidates(path), key=lambda p: (_frame_sort_key(p), _candidate_score(p)))
    sources: list[DerivedFrameSource] = []
    for ordinal, file_path in enumerate(candidates[:frame_limit]):
        data = _load_npz(file_path)
        if "lambda2" not in data:
            raise KeyError(f"{file_path}:missing lambda2")
        sources.append(DerivedFrameSource(frame=ordinal, path=file_path, data=data))
    return sources


def _load_velocity_components(data: dict[str, np.ndarray], frame: int | None) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
    if "velocity_snapshots" in data:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        if velocity.ndim == 5:
            if velocity.shape[-1] != 3:
                raise ValueError(f"velocity_snapshots must end in a component axis of size 3, got {velocity.shape!r}")
            if frame is None:
                if int(velocity.shape[0]) != 1:
                    raise ValueError(f"velocity_snapshots has {velocity.shape[0]} frame(s); pass --frame")
                velocity = velocity[0]
            else:
                if frame < 0 or frame >= int(velocity.shape[0]):
                    raise ValueError(f"velocity_snapshots frame {frame} is out of range for {velocity.shape[0]} frame(s)")
                velocity = velocity[frame]
        elif velocity.ndim == 4 and velocity.shape[-1] == 3:
            if frame is not None:
                raise ValueError("velocity_snapshots has no frame axis; omit --frame")
        else:
            raise ValueError(f"velocity_snapshots must be 4D or 5D with a final component axis, got {velocity.shape!r}")
        if velocity.ndim != 4 or velocity.shape[-1] != 3:
            raise ValueError(f"velocity_snapshots must be 4D after frame selection, got {velocity.shape!r}")
        if not np.all(np.isfinite(velocity)):
            raise ValueError("velocity_snapshots contains non-finite values")
        return (
            np.asarray(velocity[..., 0], dtype=np.float64),
            np.asarray(velocity[..., 1], dtype=np.float64),
            np.asarray(velocity[..., 2], dtype=np.float64),
            "velocity_snapshots",
        )

    if all(key in data for key in ("u", "v", "w")):
        return (
            _load_frame_field("u", data["u"], frame),
            _load_frame_field("v", data["v"], frame),
            _load_frame_field("w", data["w"], frame),
            "u/v/w",
        )

    if all(key in data for key in ("u_hat", "v_hat", "w_hat")):
        components: list[np.ndarray] = []
        for name in ("u_hat", "v_hat", "w_hat"):
            spectral = np.asarray(data[name], dtype=np.complex128)
            if spectral.ndim == 4:
                if frame is None:
                    if int(spectral.shape[0]) != 1:
                        raise ValueError(f"{name} has {spectral.shape[0]} frame(s); pass --frame")
                    spectral = spectral[0]
                else:
                    if frame < 0 or frame >= int(spectral.shape[0]):
                        raise ValueError(f"{name} frame {frame} is out of range for {spectral.shape[0]} frame(s)")
                    spectral = spectral[frame]
            if spectral.ndim != 3:
                raise ValueError(f"{name} must be 3D or 4D, got {spectral.shape!r}")
            components.append(np.asarray(np.fft.ifftn(spectral, axes=(0, 1, 2)).real, dtype=np.float64))
        if not all(arr.shape == components[0].shape for arr in components[1:]):
            raise ValueError("spectral velocity component shapes do not match")
        if not all(np.all(np.isfinite(arr)) for arr in components):
            raise ValueError("spectral velocity components contain non-finite values")
        return components[0], components[1], components[2], "u_hat/v_hat/w_hat"

    raise KeyError("missing velocity field")


def _axis_wavenumbers(n: int, domain_length: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    return k.reshape(n, 1, 1), k.reshape(1, n, 1), k.reshape(1, 1, n)


def _spectral_derivative(field: np.ndarray, axis: int, kx: np.ndarray, ky: np.ndarray, kz: np.ndarray) -> np.ndarray:
    field_hat = np.fft.fftn(field, axes=(0, 1, 2))
    if axis == 0:
        return np.fft.ifftn(1j * kx * field_hat, axes=(0, 1, 2)).real
    if axis == 1:
        return np.fft.ifftn(1j * ky * field_hat, axes=(0, 1, 2)).real
    if axis == 2:
        return np.fft.ifftn(1j * kz * field_hat, axes=(0, 1, 2)).real
    raise ValueError(f"axis must be 0, 1, or 2; got {axis}")


def _validate_cubic(array: np.ndarray, name: str) -> int:
    if array.ndim != 3:
        raise ValueError(f"{name} must be 3D after frame selection, got {array.shape!r}")
    n = int(array.shape[0])
    if int(array.shape[1]) != n or int(array.shape[2]) != n:
        raise ValueError(f"{name} must be cubic, got {array.shape!r}")
    if n <= 1:
        raise ValueError(f"{name} must have size > 1, got {n}")
    return n


def _curl_norm_sq_from_velocity(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    n = _validate_cubic(u, "u")
    if v.shape != u.shape or w.shape != u.shape:
        raise ValueError(f"velocity component shapes must match, got {u.shape!r}, {v.shape!r}, {w.shape!r}")
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
    omega_x = dw_dy - dv_dz
    omega_y = du_dz - dw_dx
    omega_z = dv_dx - du_dy
    omega_sq = omega_x * omega_x + omega_y * omega_y + omega_z * omega_z
    if not np.all(np.isfinite(omega_sq)):
        raise ValueError("computed omega_norm_sq contains non-finite values")
    return np.asarray(omega_sq, dtype=np.float64)


def _load_omega_norm_sq(data: dict[str, np.ndarray], frame: int | None, domain_length: float) -> tuple[np.ndarray, str]:
    if "omega_norm_sq" in data:
        return _load_frame_field("omega_norm_sq", data["omega_norm_sq"], frame), "omega_norm_sq"

    if "omega_snapshots" in data:
        omega = np.asarray(data["omega_snapshots"], dtype=np.float64)
        if omega.ndim == 5:
            if omega.shape[-1] == 3:
                if frame is None:
                    if int(omega.shape[0]) != 1:
                        raise ValueError(f"omega_snapshots has {omega.shape[0]} frame(s); pass --frame")
                    omega = omega[0]
                else:
                    if frame < 0 or frame >= int(omega.shape[0]):
                        raise ValueError(f"omega_snapshots frame {frame} is out of range for {omega.shape[0]} frame(s)")
                    omega = omega[frame]
                if omega.ndim != 4:
                    raise ValueError(f"omega_snapshots must be 4D after frame selection, got {omega.shape!r}")
                omega_sq = np.sum(omega * omega, axis=-1, dtype=np.float64)
                return np.asarray(omega_sq, dtype=np.float64), "omega_snapshots[...,3]"
            if omega.shape[1] == 3:
                if frame is None:
                    if int(omega.shape[0]) != 1:
                        raise ValueError(f"omega_snapshots has {omega.shape[0]} frame(s); pass --frame")
                    omega = omega[0]
                else:
                    if frame < 0 or frame >= int(omega.shape[0]):
                        raise ValueError(f"omega_snapshots frame {frame} is out of range for {omega.shape[0]} frame(s)")
                    omega = omega[frame]
                if omega.ndim != 4:
                    raise ValueError(f"omega_snapshots must be 4D after frame selection, got {omega.shape!r}")
                omega_sq = np.sum(omega * omega, axis=0, dtype=np.float64)
                return np.asarray(omega_sq, dtype=np.float64), "omega_snapshots[3,...]"
            if omega.shape[0] == 3 and frame is None:
                omega_sq = np.sum(omega * omega, axis=0, dtype=np.float64)
                return np.asarray(omega_sq, dtype=np.float64), "omega_snapshots[3,...]"
        if omega.ndim == 4:
            if frame is not None:
                if omega.shape[-1] == 3:
                    if frame < 0 or frame >= int(omega.shape[0]):
                        raise ValueError(f"omega_snapshots frame {frame} is out of range for {omega.shape[0]} frame(s)")
                    omega = omega[frame]
                    return np.sum(omega * omega, axis=-1, dtype=np.float64), "omega_snapshots[...,3]"
                if omega.shape[0] == 3:
                    raise ValueError("omega_snapshots has no frame axis; omit --frame")
            if omega.shape[-1] == 3:
                if int(omega.shape[0]) == omega.shape[1] == omega.shape[2]:
                    return np.sum(omega * omega, axis=-1, dtype=np.float64), "omega_snapshots[...,3]"
                if int(omega.shape[0]) == 1:
                    omega = omega[0]
                    return np.sum(omega * omega, axis=-1, dtype=np.float64), "omega_snapshots[...,3]"
                raise ValueError(f"omega_snapshots has ambiguous 4D shape {omega.shape!r}; pass --frame or use omega_norm_sq")
            if omega.shape[0] == 3:
                return np.sum(omega * omega, axis=0, dtype=np.float64), "omega_snapshots[3,...]"
        if omega.ndim == 3:
            return np.asarray(omega * omega, dtype=np.float64), "omega_snapshots"
        raise ValueError(f"omega_snapshots has unsupported shape {omega.shape!r}")

    for key_set in OMEGA_COMPONENT_SETS:
        if all(key in data for key in key_set):
            components = [_load_frame_field(f"omega component {key}", data[key], frame) for key in key_set]
            if not all(arr.shape == components[0].shape for arr in components[1:]):
                raise ValueError("omega component shapes do not match")
            if not all(np.all(np.isfinite(arr)) for arr in components):
                raise ValueError("omega component contains non-finite values")
            omega_sq = components[0] * components[0] + components[1] * components[1] + components[2] * components[2]
            return np.asarray(omega_sq, dtype=np.float64), "+".join(key_set)

    if "velocity_snapshots" in data or all(key in data for key in ("u", "v", "w")) or all(
        key in data for key in ("u_hat", "v_hat", "w_hat")
    ):
        u, v, w, source = _load_velocity_components(data, frame)
        return _curl_norm_sq_from_velocity(u, v, w, domain_length), f"{source}->curl"

    raise KeyError("missing vorticity field")


def _resolve_domain_length(
    raw_data: dict[str, np.ndarray],
    derived_data: dict[str, np.ndarray],
    override: float | None,
    grid_size: int,
) -> tuple[float, str]:
    if override is not None:
        value = _finite_float(override, "--domain-length")
        if value <= 0.0:
            raise ValueError("--domain-length must be positive")
        return value, "cli"

    raw_len, raw_key = _scalar_metadata(raw_data, "domain_length", "length")
    derived_len, derived_key = _scalar_metadata(derived_data, "domain_length", "length")
    raw_spacing, raw_spacing_key = _scalar_metadata(raw_data, "grid_spacing", "dx")
    derived_spacing, derived_spacing_key = _scalar_metadata(derived_data, "grid_spacing", "dx")

    if raw_len is not None and _finite_float(raw_len, raw_key or "domain_length") <= 0.0:
        raise ValueError("raw domain_length must be positive")
    if derived_len is not None and _finite_float(derived_len, derived_key or "domain_length") <= 0.0:
        raise ValueError("derived domain_length must be positive")

    if raw_len is not None and derived_len is not None:
        raw_value = _finite_float(raw_len, raw_key or "domain_length")
        derived_value = _finite_float(derived_len, derived_key or "domain_length")
        if not math.isclose(raw_value, derived_value, rel_tol=1.0e-12, abs_tol=1.0e-12):
            raise ValueError("raw and derived domain_length metadata mismatch")
        return raw_value, f"raw:{raw_key or 'domain_length'}+derived:{derived_key or 'domain_length'}"
    if raw_len is not None:
        return _finite_float(raw_len, raw_key or "domain_length"), f"raw:{raw_key or 'domain_length'}"
    if derived_len is not None:
        return _finite_float(derived_len, derived_key or "domain_length"), f"derived:{derived_key or 'domain_length'}"

    if raw_spacing is not None and _finite_float(raw_spacing, raw_spacing_key or "grid_spacing") > 0.0:
        return _finite_float(raw_spacing, raw_spacing_key or "grid_spacing") * float(grid_size), f"raw:{raw_spacing_key or 'grid_spacing'}"
    if derived_spacing is not None and _finite_float(derived_spacing, derived_spacing_key or "grid_spacing") > 0.0:
        return _finite_float(derived_spacing, derived_spacing_key or "grid_spacing") * float(grid_size), f"derived:{derived_spacing_key or 'grid_spacing'}"

    return DEFAULT_DOMAIN_LENGTH, "default"


def _region_masks(lambda2: np.ndarray) -> dict[str, np.ndarray]:
    finite = np.isfinite(lambda2)
    if not np.all(finite):
        raise ValueError("lambda2 contains non-finite values")
    return {
        "lambda2_lt_-10": lambda2 < -10.0,
        "lambda2_-10_to_-3": (lambda2 >= -10.0) & (lambda2 < -3.0),
        "lambda2_-3_to_-1": (lambda2 >= -3.0) & (lambda2 < -1.0),
        "lambda2_-1_to_-0.1": (lambda2 >= -1.0) & (lambda2 < -0.1),
        "lambda2_-0.1_to_0.1": (lambda2 >= -0.1) & (lambda2 <= 0.1),
        "lambda2_0.1_to_1": (lambda2 > 0.1) & (lambda2 <= 1.0),
        "lambda2_1_to_3": (lambda2 > 1.0) & (lambda2 <= 3.0),
        "lambda2_3_to_10": (lambda2 > 3.0) & (lambda2 <= 10.0),
        "lambda2_gt_10": lambda2 > 10.0,
        "lambda2_negative_total": lambda2 < 0.0,
        "lambda2_near_zero_total": np.abs(lambda2) <= 0.1,
        "lambda2_positive_total": lambda2 > 0.0,
    }


def _build_rows(
    raw_bundle: ArchiveBundle,
    derived_sources: list[DerivedFrameSource],
    frame_limit: int,
) -> tuple[list[dict[str, Any]], list[str]]:
    warnings: list[str] = []
    rows: list[dict[str, Any]] = []
    if raw_bundle.frame_count < len(derived_sources):
        raise ValueError(
            f"frame count mismatch between raw ({raw_bundle.frame_count}) and derived ({len(derived_sources)}) archives"
        )

    frame_count = min(frame_limit, raw_bundle.frame_count, len(derived_sources))
    if frame_count < frame_limit:
        warnings.append(f"frame_limit_truncated_to_available_{frame_count}")

    for frame in range(frame_count):
        source = derived_sources[frame]
        row: dict[str, Any] = {
            "frame": int(frame),
            "status": OK_STATUS,
            "source_path": str(source.path),
            "region_sums": {},
            "region_fractions": {},
            "region_cell_counts": {},
        }
        try:
            lambda2 = _load_frame_field("lambda2", source.data["lambda2"], None)
            domain_length, domain_length_source = _resolve_domain_length(raw_bundle.data, source.data, None, int(lambda2.shape[0]))
            omega_sq, omega_source = _load_omega_norm_sq(raw_bundle.data, frame, domain_length)
            if lambda2.shape != omega_sq.shape:
                raise ValueError(f"lambda2 shape {lambda2.shape!r} does not match omega_norm_sq {omega_sq.shape!r}")
            if not np.all(np.isfinite(omega_sq)):
                raise ValueError("omega_norm_sq contains non-finite values")

            total_omega_sq = float(np.sum(omega_sq, dtype=np.float64))
            if not math.isfinite(total_omega_sq) or total_omega_sq <= 0.0:
                raise ValueError("total omega_norm_sq must be positive and finite")

            masks = _region_masks(lambda2)
            partition_sum = 0.0
            row.update(
                {
                    "shape": [int(v) for v in lambda2.shape],
                    "domain_length": float(domain_length),
                    "domain_length_source": domain_length_source,
                    "omega_norm_sq_source": omega_source,
                    "lambda2_source": "lambda2",
                    "total_omega_norm_sq": total_omega_sq,
                }
            )

            coverage = np.zeros_like(lambda2, dtype=np.int8)
            for name, _label in REGION_SPECS:
                if name not in masks:
                    continue
                mask = np.asarray(masks[name], dtype=bool)
                if name in PARTITION_REGION_NAMES:
                    coverage += mask.astype(np.int8)
                region_sum = float(np.sum(omega_sq[mask], dtype=np.float64))
                if not math.isfinite(region_sum):
                    raise ValueError(f"non-finite sum for {name}")
                region_fraction = region_sum / total_omega_sq
                if not math.isfinite(region_fraction):
                    raise ValueError(f"non-finite fraction for {name}")
                if name in PARTITION_REGION_NAMES:
                    partition_sum += region_fraction
                row["region_sums"][name] = float(region_sum)
                row["region_fractions"][name] = float(region_fraction)
                row["region_cell_counts"][name] = int(np.count_nonzero(mask))

            if not np.all(coverage == 1):
                raise ValueError("lambda2 partition masks do not form an exact cover")
            if not math.isfinite(partition_sum):
                raise ValueError("partition fraction sum is not finite")

            row["partition_fraction_sum"] = float(partition_sum)
        except Exception as exc:
            row["status"] = ERROR_STATUS
            row["errors"] = [f"{type(exc).__name__}:{exc}"]
        rows.append(row)

    return rows, sorted(set(warnings))


def _summary(
    rows: list[dict[str, Any]],
    requested_frame_limit: int,
    raw_frame_count: int,
    derived_frame_count: int,
) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def collect(region_name: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            fractions = row.get("region_fractions")
            if not isinstance(fractions, dict) or region_name not in fractions:
                continue
            value = float(fractions[region_name])
            if math.isfinite(value):
                values.append(value)
        return values

    region_stats: dict[str, dict[str, Any]] = {}
    for name, label in REGION_SPECS:
        values = collect(name)
        region_stats[name] = {
            "label": label,
            "frame_count": int(len(values)),
            "min": None if not values else float(min(values)),
            "mean": None if not values else float(sum(values) / len(values)),
            "max": None if not values else float(max(values)),
        }

    partition_values = [
        float(row["partition_fraction_sum"])
        for row in ok_rows
        if isinstance(row.get("partition_fraction_sum"), (int, float))
        and math.isfinite(float(row["partition_fraction_sum"]))
    ]

    return {
        "requested_frame_limit": int(requested_frame_limit),
        "raw_frame_count": int(raw_frame_count),
        "derived_frame_count": int(derived_frame_count),
        "shared_frame_count": int(min(raw_frame_count, derived_frame_count)),
        "processed_frame_count": int(len(rows)),
        "ok_frame_count": int(len(ok_rows)),
        "status_counts": {
            status: sum(1 for row in rows if str(row.get("status", ERROR_STATUS)) == status)
            for status in sorted({str(row.get("status", ERROR_STATUS)) for row in rows})
        },
        "region_stats": region_stats,
        "partition_fraction_sum_min": None if not partition_values else float(min(partition_values)),
        "partition_fraction_sum_mean": None if not partition_values else float(sum(partition_values) / len(partition_values)),
        "partition_fraction_sum_max": None if not partition_values else float(max(partition_values)),
        "all_frames_ok": bool(len(ok_rows) == len(rows) and len(rows) > 0),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--raw-archive", type=Path, required=True, help="raw NPZ archive containing omega_norm_sq or raw vorticity data")
    parser.add_argument(
        "--derived-archive",
        type=Path,
        required=True,
        help="directory of per-frame derived NPZ archives containing lambda2",
    )
    parser.add_argument(
        "--frame-limit",
        type=_positive_int,
        default=DEFAULT_FRAME_LIMIT,
        help="maximum number of aligned frames to process",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="JSON output path",
    )
    parser.add_argument("--pretty", action="store_true", help="pretty-print the JSON output")
    return parser.parse_args()


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    payload: dict[str, Any] = {
        "schema_version": 1,
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        "status": OK_STATUS,
        "raw_archive": str(args.raw_archive),
        "derived_archive": str(args.derived_archive),
        "output_json": str(args.output_json),
        "frame_limit": int(args.frame_limit),
        "warnings": [],
        "errors": [],
        "rows": [],
        "region_specs": [{"name": name, "label": label} for name, label in REGION_SPECS],
        "O": "Emit per-frame signed lambda2 partition fractions from raw omega_norm_sq and derived lambda2 archives.",
        "R": "Measure how much total omega_norm_sq lies in each signed lambda2 band and in the negative, near-zero, and positive totals.",
        "C": SCRIPT_NAME,
        "S": "Load the raw archive plus per-frame derived lambda2 files, validate alignment, and fail closed on malformed or non-finite inputs.",
        "L": "Status is ok only when every processed frame has aligned shapes, finite data, and an exact region cover.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or runtime authority is claimed by this diagnostic.",
        "F": "Empirical only; it does not promote any proof or claim.",
        "changed_paths": [str(args.output_json)],
    }

    try:
        raw_bundle = _load_bundle(args.raw_archive)
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"raw_archive:{type(exc).__name__}:{exc}"]
        return payload, 1

    try:
        derived_sources = _load_derived_sources(args.derived_archive, int(args.frame_limit))
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"derived_archive:{type(exc).__name__}:{exc}"]
        return payload, 1

    try:
        rows, warnings = _build_rows(raw_bundle, derived_sources, int(args.frame_limit))
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"{type(exc).__name__}:{exc}"]
        return payload, 1

    payload["raw_archive"] = str(raw_bundle.path)
    payload["derived_archive"] = str(args.derived_archive)
    payload["rows"] = rows
    payload["warnings"] = sorted(set(warnings))
    payload["summary"] = _summary(rows, int(args.frame_limit), raw_bundle.frame_count, len(derived_sources))
    payload["errors"] = sorted(
        {
            str(row.get("status"))
            for row in rows
            if str(row.get("status", OK_STATUS)) != OK_STATUS
        }
    )

    row_statuses = [str(row.get("status", OK_STATUS)) for row in rows]
    if rows and all(status == OK_STATUS for status in row_statuses):
        payload["status"] = OK_STATUS
    else:
        payload["status"] = ERROR_STATUS
    return payload, 0 if payload["status"] == OK_STATUS else 1


def main() -> int:
    args = parse_args()
    payload, exit_code = _build_payload(args)
    text = _json_text(payload, bool(args.pretty))
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    print(text)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
