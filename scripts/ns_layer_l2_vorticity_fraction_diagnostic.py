#!/usr/bin/env python3
"""Layer-L2 vorticity fraction diagnostic for NS boundary archives.

This script resolves a raw/derived tensor archive pair, then for each frame
computes the fraction of the total domain sum(|omega|^2) that lies in the
lambda2-carrier set ``{|lambda2| < eps}`` for each requested epsilon.

The diagnostic is fail-closed, emits deterministic JSON, and follows the
existing NS archive conventions used by the other boundary scripts:

* raw input may provide ``velocity_snapshots``, ``omega_snapshots``,
  ``omega_norm_sq``, or component fields;
* derived input must provide ``lambda2``;
* scalar metadata is recovered from ``meta_json`` or standard fields such as
  ``domain_length`` and ``grid_spacing`` when present.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_layer_l2_vorticity_fraction_diagnostic.py"
CONTRACT = "ns_layer_l2_vorticity_fraction_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_LAYER_L2_VORTICITY_FRACTION_DIAGNOSTIC"
OK_STATUS = "ok"
STATUS_MISSING = "missing_required_field"
STATUS_INVALID = "invalid_argument"
STATUS_SHAPE = "shape_mismatch"
DEFAULT_FRAME_LIMIT = 13
DEFAULT_EPSILONS = (0.001, 0.01, 0.1, 1.0)
DEFAULT_INPUT_DIR = Path("scripts/data/outputs/ns_boundary_pressure_geometric_20260619")
DEFAULT_OUTPUT = DEFAULT_INPUT_DIR / "ns_layer_l2_vorticity_fraction_N128_20260619.json"
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


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be a nonnegative integer")
    return parsed


def _positive_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed <= 0.0:
        raise argparse.ArgumentTypeError("value must be finite and positive")
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
    for name in ("lambda2", "velocity_snapshots", "omega_snapshots", "omega_norm_sq", "omega_x", "omega_y", "omega_z", "omega1", "omega2", "omega3", "w_x", "w_y", "w_z", "wx", "wy", "wz", "vorticity_x", "vorticity_y", "vorticity_z", "vorticity1", "vorticity2", "vorticity3"):
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
    import re

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
            (candidate for candidate in path.iterdir() if candidate.is_file() and candidate.suffix.lower() == ".npz"),
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
    sources = []
    for frame in range(min(frame_limit, bundle.frame_count)):
        sources.append(DerivedFrameSource(frame=frame, path=bundle.path, data=bundle.data, frame_arg=frame))
    return sources


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


def _select_velocity_components(data: dict[str, np.ndarray], frame: int | None) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
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


def _load_archive_bundle(
    explicit: Path | None,
    input_dir: Path,
    kind: str,
) -> ArchiveBundle:
    path = explicit if explicit is not None else _find_candidate_npz(input_dir, kind)
    if path.is_dir():
        path = _find_candidate_npz(path, kind)
    if not path.exists():
        raise FileNotFoundError(f"{kind} archive not found: {path}")
    if path.suffix.lower() != ".npz":
        raise ValueError(f"{kind} archive must be a .npz file, got {path}")
    return _load_bundle(path, kind)


def _frame_value(array: np.ndarray, frame: int) -> np.ndarray:
    value = np.asarray(array)
    if value.ndim == 4:
        return np.asarray(value[frame])
    return value


def _build_rows(
    raw_bundle: ArchiveBundle,
    derived_sources: list[DerivedFrameSource],
    frame_limit: int,
    epsilons: list[float],
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
        lambda2_data = source.data.get("lambda2")
        if lambda2_data is None:
            raise KeyError(f"{source.path}:missing lambda2")
        row: dict[str, Any] = {
            "frame": int(frame),
            "status": OK_STATUS,
            "source_path": str(source.path),
            "eps_rows": [],
        }
        try:
            lambda2 = _load_frame_field("lambda2", lambda2_data, source.frame_arg)
            domain_length, domain_length_source = _resolve_domain_length(
                raw_bundle.data,
                source.data,
                None,
                int(lambda2.shape[0]),
            )
            omega_sq, omega_source = _load_omega_norm_sq(raw_bundle.data, frame, domain_length)
            if lambda2.shape != omega_sq.shape:
                raise ValueError(f"lambda2 shape {lambda2.shape!r} does not match omega_norm_sq {omega_sq.shape!r}")
            if not np.all(np.isfinite(lambda2)):
                raise ValueError("lambda2 contains non-finite values")
            if not np.all(np.isfinite(omega_sq)):
                raise ValueError("omega_norm_sq contains non-finite values")

            total_omega_sq = float(np.sum(omega_sq, dtype=np.float64))
            if not math.isfinite(total_omega_sq) or total_omega_sq <= 0.0:
                raise ValueError("total omega_norm_sq must be positive and finite")

            row.update(
                {
                    "shape": [int(v) for v in lambda2.shape],
                    "domain_length": float(domain_length),
                    "domain_length_source": domain_length_source,
                    "omega_norm_sq_source": omega_source,
                    "lambda2_source": "lambda2",
                    "total_domain_omega_norm_sq": total_omega_sq,
                    "total_domain_omega_norm": float(math.sqrt(total_omega_sq)),
                }
            )

            previous_fraction = -1.0
            for eps in epsilons:
                carrier_mask = np.abs(lambda2) < float(eps)
                carrier_count = int(np.count_nonzero(carrier_mask))
                carrier_omega_sq = float(np.sum(omega_sq[carrier_mask], dtype=np.float64))
                fraction = carrier_omega_sq / total_omega_sq
                if not math.isfinite(fraction):
                    raise ValueError(f"non-finite fraction for eps={eps}")
                if fraction + 1.0e-12 < previous_fraction:
                    warnings.append(f"nonmonotone_fraction_frame_{frame}_eps_{eps:g}")
                previous_fraction = max(previous_fraction, fraction)
                row["eps_rows"].append(
                    {
                        "eps": float(eps),
                        "carrier_cell_count": carrier_count,
                        "carrier_cell_fraction": float(carrier_count / float(lambda2.size)),
                        "carrier_omega_norm_sq": carrier_omega_sq,
                        "carrier_omega_norm": float(math.sqrt(carrier_omega_sq)),
                        "fraction_of_total_omega_norm_sq": float(fraction),
                    }
                )
        except Exception as exc:
            row["status"] = STATUS_MISSING if isinstance(exc, KeyError) else STATUS_SHAPE if isinstance(exc, ValueError) else STATUS_INVALID
            row["errors"] = [f"{type(exc).__name__}:{exc}"]
        rows.append(row)

    return rows, sorted(set(warnings))


def _summary(rows: list[dict[str, Any]], epsilons: list[float], requested_frame_limit: int, available_frame_count: int) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def collect(eps_index: int) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            eps_rows = row.get("eps_rows")
            if not isinstance(eps_rows, list) or eps_index >= len(eps_rows):
                continue
            value = eps_rows[eps_index].get("fraction_of_total_omega_norm_sq")
            if value is None:
                continue
            number = float(value)
            if math.isfinite(number):
                values.append(number)
        return values

    eps_stats: dict[str, dict[str, float | int | None]] = {}
    for index, eps in enumerate(epsilons):
        values = collect(index)
        eps_stats[str(eps)] = {
            "eps": float(eps),
            "frame_count": int(len(values)),
            "min": None if not values else float(min(values)),
            "mean": None if not values else float(sum(values) / len(values)),
            "max": None if not values else float(max(values)),
            "median": None if not values else float(np.median(np.asarray(values, dtype=np.float64))),
        }

    total_values = [
        float(row["total_domain_omega_norm_sq"])
        for row in ok_rows
        if isinstance(row.get("total_domain_omega_norm_sq"), (int, float))
        and math.isfinite(float(row["total_domain_omega_norm_sq"]))
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
        "eps_stats": eps_stats,
        "all_frames_ok": bool(len(ok_rows) == len(rows) and len(rows) > 0),
        "total_omega_l2_sq_min": None if not total_values else float(min(total_values)),
        "total_omega_l2_sq_mean": None if not total_values else float(sum(total_values) / len(total_values)),
        "total_omega_l2_sq_max": None if not total_values else float(max(total_values)),
        "monotone_eps_fraction": all(
            (eps_stats[str(epsilons[i])]["max"] is None or eps_stats[str(epsilons[i + 1])]["min"] is None)
            or float(eps_stats[str(epsilons[i])]["max"]) <= float(eps_stats[str(epsilons[i + 1])]["max"]) + 1.0e-12
            for i in range(max(0, len(epsilons) - 1))
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
    eps_stats = summary.get("eps_stats", {})
    if isinstance(eps_stats, dict):
        for key in sorted(eps_stats.keys()):
            item = eps_stats.get(key, {})
            if isinstance(item, dict):
                lines.append(
                    f"eps {key}: min={item.get('min')} mean={item.get('mean')} max={item.get('max')}"
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
    parser.add_argument(
        "--input-dir",
        type=Path,
        default=DEFAULT_INPUT_DIR,
        help="Directory used to locate raw/derived NPZ archives when explicit paths are omitted.",
    )
    parser.add_argument(
        "--raw-archive",
        type=Path,
        default=None,
        help="Raw NPZ archive or directory containing the raw archive.",
    )
    parser.add_argument(
        "--derived-archive",
        type=Path,
        default=None,
        help="Derived tensor NPZ archive or directory containing the derived archive.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="JSON output path.",
    )
    parser.add_argument(
        "--eps",
        type=_positive_float,
        nargs="+",
        default=list(DEFAULT_EPSILONS),
        help="Positive epsilon thresholds for the |lambda2| carrier mask.",
    )
    parser.add_argument(
        "--frame-limit",
        type=_positive_int,
        default=DEFAULT_FRAME_LIMIT,
        help="Maximum number of frames to process from the archive pair.",
    )
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="Optional override for the domain side length used when deriving omega from velocity.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON output.")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout as well as writing the file.")
    return parser.parse_args()


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    payload: dict[str, Any] = {
        "status": OK_STATUS,
        "schema_version": 1,
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        "input_dir": str(args.input_dir),
        "raw_archive": None if args.raw_archive is None else str(args.raw_archive),
        "derived_archive": None if args.derived_archive is None else str(args.derived_archive),
        "output_json": str(args.output_json),
        "eps": [float(value) for value in args.eps],
        "eps_bands": [float(value) for value in args.eps],
        "frame_limit": int(args.frame_limit),
        "domain_length_override": None if args.domain_length is None else float(args.domain_length),
        "warnings": [],
        "errors": [],
        "rows": [],
        "O": "Emit per-frame Layer-L2 vorticity concentration fractions from NS boundary archives.",
        "R": "Measure how much of total sum(|omega|^2) lies in cells with |lambda2| < eps for each frame.",
        "C": SCRIPT_NAME,
        "S": "Resolve raw and derived NPZ archives, align frames, compute vorticity-square fractions, and fail closed on malformed inputs.",
        "L": "Status is ok only when the archives, frame count, and required fields are usable for every processed frame.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or runtime authority is claimed by this diagnostic.",
        "F": "The run is empirical only and does not promote any proof or claim.",
        "changed_paths": [str(args.output_json)],
    }

    if not args.eps:
        payload["status"] = STATUS_INVALID
        payload["errors"] = ["empty_eps_list"]
        return payload, 1

    try:
        raw_bundle = _load_archive_bundle(args.raw_archive, args.input_dir, "raw")
    except Exception as exc:
        payload["status"] = STATUS_MISSING
        payload["errors"] = [f"raw_archive:{type(exc).__name__}:{exc}"]
        return payload, 1

    try:
        derived_path = args.derived_archive if args.derived_archive is not None else _find_candidate_npz(args.input_dir, "derived")
        if derived_path.is_dir():
            payload["derived_archive"] = str(derived_path)
        else:
            payload["derived_archive"] = str(derived_path)
        derived_sources = _load_derived_sources(derived_path, int(args.frame_limit))
    except Exception as exc:
        payload["status"] = STATUS_MISSING
        payload["errors"] = [f"derived_archive:{type(exc).__name__}:{exc}"]
        return payload, 1

    try:
        if not derived_sources:
            raise ValueError("no derived sources selected")
        if args.domain_length is not None:
            # Store the override in the raw bundle metadata for the per-frame resolver.
            raw_bundle.data["domain_length"] = np.asarray(float(args.domain_length))
        rows, warnings = _build_rows(
            raw_bundle=raw_bundle,
            derived_sources=derived_sources,
            frame_limit=int(args.frame_limit),
            epsilons=[float(value) for value in args.eps],
        )
    except Exception as exc:
        payload["status"] = STATUS_SHAPE if isinstance(exc, ValueError) else STATUS_MISSING
        payload["errors"] = [f"{type(exc).__name__}:{exc}"]
        return payload, 1

    payload["rows"] = rows
    payload["summary"] = _summary(rows, [float(value) for value in args.eps], int(args.frame_limit), raw_bundle.frame_count)
    if payload["summary"].get("total_omega_l2_sq_min") is not None:
        payload["total_omega_l2_sq"] = payload["summary"]["total_omega_l2_sq_min"]
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
        payload["derived_archive"] = str(first_path.parent if all(source.path.parent == first_path.parent for source in derived_sources) and len(derived_sources) > 1 else first_path)
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
    if args.json:
        print(text)
    else:
        print(_render_text(payload))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
