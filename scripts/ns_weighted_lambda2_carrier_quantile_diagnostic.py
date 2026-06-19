#!/usr/bin/env python3
"""Weighted |lambda2| carrier quantile diagnostic for NS boundary archives.

This runner consumes a raw NPZ archive plus the derived per-frame archive
layout used by ``scripts/ns_layer_l2_vorticity_fraction_diagnostic.py`` and
computes, for each frame, the smallest ``eps`` such that the
``omega_norm_sq``-weighted carrier set ``{|lambda2| <= eps}`` captures each
requested target fraction of the total ``omega_norm_sq`` mass.

The output is deterministic and fail-closed. Every frame row records the
threshold needed for each target fraction together with the achieved carrier
mass at that threshold. Aggregate statistics report min/mean/max
``eps_needed`` per target across the ok frames.
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


SCRIPT_NAME = "scripts/ns_weighted_lambda2_carrier_quantile_diagnostic.py"
CONTRACT = "ns_weighted_lambda2_carrier_quantile_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_WEIGHTED_LAMBDA2_CARRIER_QUANTILE_DIAGNOSTIC"
OK_STATUS = "ok"
STATUS_MISSING = "missing_required_field"
STATUS_INVALID = "invalid_argument"
STATUS_SHAPE = "shape_mismatch"
DEFAULT_FRAME_LIMIT = 13
DEFAULT_TARGETS = (0.05, 0.10, 0.25, 0.50, 0.75, 0.90)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260619/"
    "ns_weighted_lambda2_carrier_quantile_N128_20260619.json"
)
DEFAULT_DOMAIN_LENGTH = 2.0 * math.pi
OMEGA_COMPONENT_SETS = (
    ("omega_x", "omega_y", "omega_z"),
    ("omega1", "omega2", "omega3"),
    ("w_x", "w_y", "w_z"),
    ("wx", "wy", "wz"),
    ("vorticity_x", "vorticity_y", "vorticity_z"),
    ("vorticity1", "vorticity2", "vorticity3"),
)


@dataclass(frozen=True)
class ArchiveBundle:
    path: Path
    data: dict[str, np.ndarray]
    frame_count: int
    source_kind: str


@dataclass(frozen=True)
class DerivedFrameSource:
    frame: int
    path: Path
    data: dict[str, np.ndarray]
    frame_arg: int | None


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def _target_fraction(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0 or parsed > 1.0:
        raise argparse.ArgumentTypeError("target fractions must lie in [0, 1]")
    return parsed


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return float(parsed)


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
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


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


def _finite_scalar_metadata(data: dict[str, np.ndarray], *names: str) -> tuple[float | None, str | None]:
    value, key = _scalar_metadata(data, *names)
    if value is None:
        return None, None
    return _finite_float(value, key or names[0]), key


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
    for name in (
        "lambda2",
        "velocity_snapshots",
        "omega_snapshots",
        "omega_norm_sq",
        "omega_x",
        "omega_y",
        "omega_z",
        "omega1",
        "omega2",
        "omega3",
        "w_x",
        "w_y",
        "w_z",
        "wx",
        "wy",
        "wz",
        "vorticity_x",
        "vorticity_y",
        "vorticity_z",
        "vorticity1",
        "vorticity2",
        "vorticity3",
    ):
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


def _candidate_score(path: Path, kind: str) -> tuple[int, str]:
    stem = path.stem.lower()
    score = 0
    if kind == "raw":
        if "raw" in stem:
            score += 3
        if "velocity" in stem or "omega" in stem:
            score += 2
    else:
        if "derived" in stem or "tensor" in stem:
            score += 3
        if "lambda2" in stem or "boundary" in stem:
            score += 2
    if "frame" in stem:
        score += 1
    return score, path.name


def _find_candidate_npz(directory: Path, kind: str) -> Path:
    if not directory.exists():
        raise FileNotFoundError(f"input directory not found: {directory}")
    if directory.is_file():
        if directory.suffix.lower() != ".npz":
            raise ValueError(f"expected a .npz archive, got {directory}")
        return directory

    candidates = [path for path in directory.rglob("*.npz") if path.is_file()]
    if not candidates:
        raise FileNotFoundError(f"no .npz archives found under {directory}")

    scored = sorted((_candidate_score(path, kind), path) for path in candidates)
    best_score = scored[-1][0][0]
    best = [path for score, path in scored if score[0] == best_score]
    if not best:
        raise FileNotFoundError(f"no candidate {kind} archive found under {directory}")
    return sorted(best)[0]


def _frame_sort_key(path: Path) -> tuple[int, str]:
    match = re.search(r"(?:frame[_-]?|^)(\d+)(?:$|[_-])", path.stem)
    if match is not None:
        return int(match.group(1)), path.name
    return 10**12, path.name


def _load_bundle(path: Path, kind: str) -> ArchiveBundle:
    data = _load_npz(path)
    frame_count = _extract_frame_count(data)
    return ArchiveBundle(path=path, data=data, frame_count=frame_count, source_kind=kind)


def _load_derived_sources(path: Path, frame_limit: int) -> list[DerivedFrameSource]:
    if path.is_dir():
        files = sorted(
            (
                candidate
                for candidate in path.iterdir()
                if candidate.is_file() and candidate.suffix.lower() == ".npz"
            ),
            key=_frame_sort_key,
        )
        if not files:
            raise FileNotFoundError(f"no .npz archives found in derived directory: {path}")
        sources: list[DerivedFrameSource] = []
        for ordinal, file_path in enumerate(files[:frame_limit]):
            data = _load_npz(file_path)
            if "lambda2" not in data:
                raise KeyError(f"{file_path}:missing lambda2")
            sources.append(DerivedFrameSource(frame=ordinal, path=file_path, data=data, frame_arg=None))
        return sources

    bundle = _load_bundle(path, "derived")
    sources: list[DerivedFrameSource] = []
    for frame in range(min(frame_limit, bundle.frame_count)):
        sources.append(DerivedFrameSource(frame=frame, path=bundle.path, data=bundle.data, frame_arg=frame))
    return sources


def _load_frame_count(path: Path) -> int:
    if path.is_dir():
        files = sorted(
            (candidate for candidate in path.iterdir() if candidate.is_file() and candidate.suffix.lower() == ".npz"),
            key=_frame_sort_key,
        )
        return len(files)
    return _load_bundle(path, "derived").frame_count


def _extract_scalar_field(
    data: dict[str, np.ndarray],
    name: str,
    frame: int | None,
    *,
    required: bool = True,
) -> np.ndarray | None:
    if name not in data:
        if required:
            raise KeyError(name)
        return None
    return _load_frame_field(name, data[name], frame)


def _select_velocity_components(
    data: dict[str, np.ndarray],
    frame: int | None,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
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
        u = _extract_scalar_field(data, "u", frame)
        v = _extract_scalar_field(data, "v", frame)
        w = _extract_scalar_field(data, "w", frame)
        assert u is not None and v is not None and w is not None
        return u, v, w, "u/v/w"

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


def _load_omega_norm_sq(
    data: dict[str, np.ndarray],
    frame: int | None,
    domain_length: float,
) -> tuple[np.ndarray, str]:
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
                if omega.shape[0] != 3 and omega.shape[-1] != 3 and int(omega.shape[0]) > 1:
                    if frame < 0 or frame >= int(omega.shape[0]):
                        raise ValueError(f"omega_snapshots frame {frame} is out of range for {omega.shape[0]} frame(s)")
                    omega = omega[frame]
                    if omega.ndim != 3:
                        raise ValueError(f"omega_snapshots scalar frame must be 3D after selection, got {omega.shape!r}")
                    return np.asarray(omega * omega, dtype=np.float64), "omega_snapshots"
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
        u, v, w, source = _select_velocity_components(data, frame)
        omega_sq = _curl_norm_sq_from_velocity(u, v, w, domain_length)
        return omega_sq, f"{source}->curl"

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

    raw_len, raw_key = _finite_scalar_metadata(raw_data, "domain_length", "length")
    derived_len, derived_key = _finite_scalar_metadata(derived_data, "domain_length", "length")
    raw_spacing, raw_spacing_key = _finite_scalar_metadata(raw_data, "grid_spacing", "dx")
    derived_spacing, derived_spacing_key = _finite_scalar_metadata(derived_data, "grid_spacing", "dx")

    raw_value = None if raw_len is None else raw_len
    derived_value = None if derived_len is None else derived_len

    if raw_value is not None and raw_value <= 0.0:
        raise ValueError("raw domain_length must be positive")
    if derived_value is not None and derived_value <= 0.0:
        raise ValueError("derived domain_length must be positive")

    if raw_value is not None and derived_value is not None:
        if not math.isclose(raw_value, derived_value, rel_tol=1.0e-12, abs_tol=1.0e-12):
            raise ValueError("raw and derived domain_length metadata mismatch")
        return raw_value, f"raw:{raw_key or 'domain_length'}+derived:{derived_key or 'domain_length'}"
    if raw_value is not None:
        return raw_value, f"raw:{raw_key or 'domain_length'}"
    if derived_value is not None:
        return derived_value, f"derived:{derived_key or 'domain_length'}"

    if raw_spacing is not None and raw_spacing > 0.0:
        return raw_spacing * float(grid_size), f"raw:{raw_spacing_key or 'grid_spacing'}"
    if derived_spacing is not None and derived_spacing > 0.0:
        return derived_spacing * float(grid_size), f"derived:{derived_spacing_key or 'grid_spacing'}"

    return DEFAULT_DOMAIN_LENGTH, "default"


def _load_archive_bundle(explicit: Path | None, input_dir: Path, kind: str) -> ArchiveBundle:
    path = explicit if explicit is not None else _find_candidate_npz(input_dir, kind)
    if path.is_dir():
        path = _find_candidate_npz(path, kind)
    if not path.exists():
        raise FileNotFoundError(f"{kind} archive not found: {path}")
    if path.suffix.lower() != ".npz":
        raise ValueError(f"{kind} archive must be a .npz file, got {path}")
    return _load_bundle(path, kind)


def _carrier_quantile_row(
    *,
    raw_bundle: ArchiveBundle,
    source: DerivedFrameSource,
    target_fractions: list[float],
) -> dict[str, Any]:
    lambda2_data = source.data.get("lambda2")
    if lambda2_data is None:
        raise KeyError(f"{source.path}:missing lambda2")
    lambda2 = _load_frame_field("lambda2", lambda2_data, source.frame_arg)
    domain_length, domain_length_source = _resolve_domain_length(raw_bundle.data, source.data, None, int(lambda2.shape[0]))
    omega_sq, omega_source = _load_omega_norm_sq(raw_bundle.data, source.frame, domain_length)
    if lambda2.shape != omega_sq.shape:
        raise ValueError(f"lambda2 shape {lambda2.shape!r} does not match omega_norm_sq {omega_sq.shape!r}")
    if not np.all(np.isfinite(lambda2)):
        raise ValueError("lambda2 contains non-finite values")
    if not np.all(np.isfinite(omega_sq)):
        raise ValueError("omega_norm_sq contains non-finite values")

    total_weight = float(np.sum(omega_sq, dtype=np.float64))
    if not math.isfinite(total_weight) or total_weight <= 0.0:
        raise ValueError("total omega_norm_sq must be positive and finite")

    abs_lambda2 = np.abs(np.asarray(lambda2, dtype=np.float64)).ravel()
    weights = np.asarray(omega_sq, dtype=np.float64).ravel()
    if abs_lambda2.size != weights.size:
        raise ValueError("lambda2 and omega_norm_sq sizes do not match")
    if np.any(weights < 0.0):
        raise ValueError("omega_norm_sq contains negative values")

    order = np.argsort(abs_lambda2, kind="mergesort")
    sorted_abs = abs_lambda2[order]
    sorted_weights = weights[order]
    cumulative = np.cumsum(sorted_weights, dtype=np.float64)

    target_rows: list[dict[str, Any]] = []
    for target in target_fractions:
        target_mass = float(target) * total_weight
        index = int(np.searchsorted(cumulative, target_mass, side="left"))
        if index >= int(sorted_abs.size):
            index = int(sorted_abs.size) - 1
        eps_needed = float(sorted_abs[index])
        carrier_mask = abs_lambda2 <= eps_needed
        carrier_weight = float(np.sum(weights[carrier_mask], dtype=np.float64))
        carrier_count = int(np.count_nonzero(carrier_mask))
        carrier_fraction = carrier_weight / total_weight
        target_rows.append(
            {
                "target": float(target),
                "eps_needed": eps_needed,
                "carrier_weight": carrier_weight,
                "carrier_weight_fraction": float(carrier_fraction),
                "carrier_weight_fraction_error": float(carrier_fraction - float(target)),
                "carrier_cell_count": carrier_count,
                "carrier_cell_fraction": float(carrier_count / float(lambda2.size)),
            }
        )

    return {
        "frame": int(source.frame),
        "status": OK_STATUS,
        "source_path": str(source.path),
        "shape": [int(v) for v in lambda2.shape],
        "domain_length": float(domain_length),
        "domain_length_source": domain_length_source,
        "omega_norm_sq_source": omega_source,
        "lambda2_source": "lambda2",
        "total_omega_norm_sq": total_weight,
        "total_omega_norm": float(math.sqrt(total_weight)),
        "target_rows": target_rows,
        "warnings": [],
        "errors": [],
    }


def _build_rows(
    raw_bundle: ArchiveBundle,
    derived_sources: list[DerivedFrameSource],
    frame_limit: int,
    target_fractions: list[float],
) -> tuple[list[dict[str, Any]], list[str]]:
    warnings: list[str] = []
    rows: list[dict[str, Any]] = []

    frame_count = min(frame_limit, raw_bundle.frame_count, len(derived_sources))
    if frame_count <= 0:
        raise ValueError("no frames available for analysis")
    if frame_count < frame_limit:
        warnings.append(f"frame_limit_truncated_to_available_{frame_count}")

    for frame in range(frame_count):
        source = derived_sources[frame]
        try:
            row = _carrier_quantile_row(raw_bundle=raw_bundle, source=source, target_fractions=target_fractions)
        except Exception as exc:
            status = STATUS_MISSING if isinstance(exc, KeyError) else STATUS_SHAPE if isinstance(exc, ValueError) else STATUS_INVALID
            row = {
                "frame": int(frame),
                "status": status,
                "source_path": str(source.path),
                "target_rows": [],
                "warnings": [],
                "errors": [f"{type(exc).__name__}:{exc}"],
            }
        rows.append(row)

    return rows, sorted(set(warnings))


def _summary(
    rows: list[dict[str, Any]],
    target_fractions: list[float],
    requested_frame_limit: int,
    available_frame_count: int,
) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def collect(target_index: int) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            target_rows = row.get("target_rows")
            if not isinstance(target_rows, list) or target_index >= len(target_rows):
                continue
            value = target_rows[target_index].get("eps_needed")
            if value is None:
                continue
            number = float(value)
            if math.isfinite(number):
                values.append(number)
        return values

    target_stats: dict[str, dict[str, float | int | None]] = {}
    for index, target in enumerate(target_fractions):
        values = collect(index)
        key = str(float(target))
        target_stats[key] = {
            "target": float(target),
            "frame_count": int(len(values)),
            "min_eps_needed": None if not values else float(min(values)),
            "mean_eps_needed": None if not values else float(sum(values) / len(values)),
            "max_eps_needed": None if not values else float(max(values)),
        }

    total_weights = [
        float(row["total_omega_norm_sq"])
        for row in ok_rows
        if isinstance(row.get("total_omega_norm_sq"), (int, float))
        and math.isfinite(float(row["total_omega_norm_sq"]))
    ]

    return {
        "requested_frame_limit": int(requested_frame_limit),
        "available_frame_count": int(available_frame_count),
        "processed_frame_count": int(len(rows)),
        "ok_frame_count": int(len(ok_rows)),
        "status_counts": {
            status: sum(1 for row in rows if str(row.get("status", STATUS_MISSING)) == status)
            for status in sorted({str(row.get("status", STATUS_MISSING)) for row in rows})
        },
        "target_stats": target_stats,
        "all_frames_ok": bool(len(ok_rows) == len(rows) and len(rows) > 0),
        "total_omega_norm_sq_min": None if not total_weights else float(min(total_weights)),
        "total_omega_norm_sq_mean": None if not total_weights else float(sum(total_weights) / len(total_weights)),
        "total_omega_norm_sq_max": None if not total_weights else float(max(total_weights)),
        "monotone_target_eps": all(
            target_stats[str(float(target_fractions[i]))]["max_eps_needed"] is None
            or target_stats[str(float(target_fractions[i + 1]))]["min_eps_needed"] is None
            or float(target_stats[str(float(target_fractions[i]))]["max_eps_needed"])
            <= float(target_stats[str(float(target_fractions[i + 1]))]["max_eps_needed"]) + 1.0e-12
            for i in range(max(0, len(target_fractions) - 1))
        ),
    }


def _render_text(payload: dict[str, Any]) -> str:
    summary = payload.get("summary", {})
    lines = [
        f"status: {payload.get('status')}",
        f"raw_archive: {payload.get('raw_archive')}",
        f"derived_archive: {payload.get('derived_archive')}",
        f"frames: {summary.get('processed_frame_count')}/{summary.get('available_frame_count')}",
    ]
    target_stats = summary.get("target_stats", {})
    if isinstance(target_stats, dict):
        for key in sorted(target_stats.keys()):
            item = target_stats.get(key, {})
            if isinstance(item, dict):
                lines.append(
                    f"target {key}: min={item.get('min_eps_needed')} "
                    f"mean={item.get('mean_eps_needed')} max={item.get('max_eps_needed')}"
                )
    warnings = payload.get("warnings", [])
    errors = payload.get("errors", [])
    if warnings:
        lines.append(f"warnings: {len(warnings)}")
    if errors:
        lines.append(f"errors: {len(errors)}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--raw-archive", type=Path, required=True, help="Raw NPZ archive or directory containing the raw archive.")
    parser.add_argument(
        "--derived-archive",
        type=Path,
        required=True,
        help="Derived per-frame directory or NPZ archive containing lambda2 fields.",
    )
    parser.add_argument(
        "--targets",
        type=_target_fraction,
        nargs="+",
        default=list(DEFAULT_TARGETS),
        help="Target carrier fractions in [0, 1].",
    )
    parser.add_argument(
        "--frame-limit",
        type=_positive_int,
        default=DEFAULT_FRAME_LIMIT,
        help="Maximum number of frames to process from the archive pair.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="JSON output path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON output.")
    return parser.parse_args()


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    target_fractions = sorted(set(float(value) for value in args.targets))
    payload: dict[str, Any] = {
        "status": OK_STATUS,
        "schema_version": 1,
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        "raw_archive": str(args.raw_archive),
        "derived_archive": str(args.derived_archive),
        "output_json": str(args.output_json),
        "targets": target_fractions,
        "frame_limit": int(args.frame_limit),
        "warnings": [],
        "errors": [],
        "rows": [],
        "O": "Emit weighted |lambda2| carrier quantiles for NS boundary archives.",
        "R": "Find the smallest |lambda2| threshold that captures each requested omega_norm_sq target fraction.",
        "C": SCRIPT_NAME,
        "S": "Load raw omega weights and derived lambda2 frames, compute weighted carrier thresholds, and fail closed on malformed inputs.",
        "L": "Status is ok only when the requested raw and derived frames are usable and every processed row is finite.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or runtime authority is claimed by this diagnostic.",
        "F": "The run is empirical only and does not promote any proof or claim.",
        "changed_paths": [str(Path(__file__).resolve())],
    }

    if not target_fractions:
        payload["status"] = STATUS_INVALID
        payload["errors"] = ["empty_targets"]
        return payload, 1
    if any((target < 0.0 or target > 1.0) for target in target_fractions):
        payload["status"] = STATUS_INVALID
        payload["errors"] = ["targets_out_of_range"]
        return payload, 1

    try:
        raw_bundle = _load_archive_bundle(args.raw_archive, args.raw_archive, "raw")
    except Exception as exc:
        payload["status"] = STATUS_MISSING
        payload["errors"] = [f"raw_archive:{type(exc).__name__}:{exc}"]
        return payload, 1

    try:
        derived_path = args.derived_archive
        if derived_path.is_dir() or not derived_path.suffix.lower() == ".npz":
            payload["derived_archive"] = str(derived_path)
        else:
            payload["derived_archive"] = str(derived_path)
        derived_available_count = _load_frame_count(derived_path)
        derived_sources = _load_derived_sources(derived_path, int(args.frame_limit))
    except Exception as exc:
        payload["status"] = STATUS_MISSING
        payload["errors"] = [f"derived_archive:{type(exc).__name__}:{exc}"]
        return payload, 1

    try:
        if not derived_sources:
            raise ValueError("no derived sources selected")
        rows, warnings = _build_rows(
            raw_bundle=raw_bundle,
            derived_sources=derived_sources,
            frame_limit=int(args.frame_limit),
            target_fractions=target_fractions,
        )
    except Exception as exc:
        payload["status"] = STATUS_SHAPE if isinstance(exc, ValueError) else STATUS_MISSING
        payload["errors"] = [f"{type(exc).__name__}:{exc}"]
        return payload, 1

    payload["rows"] = rows
    payload["summary"] = _summary(
        rows,
        target_fractions,
        int(args.frame_limit),
        min(raw_bundle.frame_count, derived_available_count),
    )
    payload["warnings"] = sorted(set(warnings))
    payload["errors"] = sorted(
        {
            str(row.get("status"))
            for row in rows
            if str(row.get("status", OK_STATUS)) != OK_STATUS
        }
    )
    payload["raw_archive"] = str(raw_bundle.path)
    if derived_sources:
        first_path = derived_sources[0].path
        payload["derived_archive"] = str(first_path.parent if derived_sources[0].frame_arg is None else first_path)
        payload["derived_frame_sources"] = [str(source.path) for source in derived_sources]

    row_statuses = [str(row.get("status", OK_STATUS)) for row in rows]
    if rows and all(status == OK_STATUS for status in row_statuses):
        payload["status"] = OK_STATUS
    elif any(status == STATUS_SHAPE for status in row_statuses):
        payload["status"] = STATUS_SHAPE
    elif any(status == STATUS_INVALID for status in row_statuses):
        payload["status"] = STATUS_INVALID
    else:
        payload["status"] = STATUS_MISSING
    return payload, 0 if payload["status"] == OK_STATUS else 1


def main() -> int:
    args = parse_args()
    payload, exit_code = _build_payload(args)
    text = _json_text(payload, bool(args.pretty))
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    print(_render_text(payload))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
