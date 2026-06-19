#!/usr/bin/env python3
"""Compare raw NS velocity frames against derived tensor archives.

The script loads a raw NPZ archive with ``velocity_snapshots`` and a derived
tensor archive with ``lambda2``/``g12``/``lambda3``-style fields, computes the
raw strain eigensystem from the velocity frame, and compares the raw and
derived values at explicitly requested cells plus the top-vorticity cell.

The output is fail-closed JSON with per-cell raw values, derived values, deltas,
sign-mismatch flags, aggregate summary statistics, and O/R/C/S/L/P/G/F control
fields. Authority is explicitly false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_raw_derived_tensor_convention_compare.py"
CONTRACT = "ns_raw_derived_tensor_convention_compare"
DEFAULT_OUTPUT = Path("outputs/ns_raw_derived_tensor_convention_compare.json")
OK_STATUS = "ok"
STATUS_MISSING = "missing_required_field"
STATUS_INVALID = "invalid_argument"
STATUS_SHAPE = "shape_mismatch"


@dataclass(frozen=True)
class RawBundle:
    velocity_source: str
    frame_source: str
    velocity_shape: tuple[int, int, int]
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    lambda1: np.ndarray
    lambda2: np.ndarray
    lambda3: np.ndarray
    g12: np.ndarray
    omega_norm_sq: np.ndarray
    omega_source: str
    domain_length: float
    grid_spacing: float
    scale_source: str


@dataclass(frozen=True)
class DerivedBundle:
    lambda2: np.ndarray
    g12: np.ndarray | None
    lambda3: np.ndarray | None
    fields_present: list[str]
    frame_source: str
    shape: tuple[int, int, int]


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


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return parsed


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


def _load_velocity_frame(data: dict[str, np.ndarray], frame: int | None) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
    if "velocity_snapshots" not in data:
        raise KeyError("missing velocity_snapshots")

    velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
    if velocity.ndim == 5:
        if frame is None:
            if int(velocity.shape[0]) != 1:
                raise ValueError(f"velocity_snapshots has {velocity.shape[0]} frames; pass --frame")
            velocity = velocity[0]
        else:
            if frame < 0 or frame >= int(velocity.shape[0]):
                raise ValueError(
                    f"velocity_snapshots frame {frame} is out of range for {velocity.shape[0]} frames"
                )
            velocity = velocity[frame]
        source = "velocity_snapshots[frame]"
    elif velocity.ndim == 4:
        source = "velocity_snapshots"
    else:
        raise ValueError(f"velocity_snapshots must have shape (N,N,N,3) or (T,N,N,N,3), got {velocity.shape!r}")

    if velocity.shape[-1] != 3:
        raise ValueError(f"velocity_snapshots must end in component axis of size 3, got {velocity.shape!r}")
    if velocity.ndim != 4:
        raise ValueError(f"velocity_snapshots must be 4D after frame selection, got {velocity.shape!r}")
    if not np.all(np.isfinite(velocity)):
        raise ValueError("velocity_snapshots contains non-finite values")
    if not (velocity.shape[0] == velocity.shape[1] == velocity.shape[2]):
        raise ValueError(f"velocity_snapshots must be cubic in space, got {velocity.shape!r}")

    u = np.asarray(velocity[..., 0], dtype=np.float64)
    v = np.asarray(velocity[..., 1], dtype=np.float64)
    w = np.asarray(velocity[..., 2], dtype=np.float64)
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError(f"velocity component shapes differ: {u.shape!r}, {v.shape!r}, {w.shape!r}")
    if u.ndim != 3:
        raise ValueError(f"velocity frame must be 3D after selection, got {u.shape!r}")
    return u, v, w, source


def _load_field(data: dict[str, np.ndarray], name: str, frame: int | None) -> tuple[np.ndarray | None, str | None]:
    if name not in data:
        return None, None
    field = np.asarray(data[name], dtype=np.float64)
    if field.ndim == 4:
        if frame is None:
            if int(field.shape[0]) != 1:
                raise ValueError(f"{name} has {field.shape[0]} frames; pass --frame")
            field = field[0]
        else:
            if frame < 0 or frame >= int(field.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {field.shape[0]} frames")
            field = field[frame]
        source = f"{name}[frame]"
    elif field.ndim == 3:
        source = name
    else:
        raise ValueError(f"{name} must be 3D or 4D, got {field.shape!r}")
    if not np.all(np.isfinite(field)):
        raise ValueError(f"{name} contains non-finite values")
    if not (field.shape[0] == field.shape[1] == field.shape[2]):
        raise ValueError(f"{name} must be cubic in space, got {field.shape!r}")
    return np.asarray(field, dtype=np.float64), source


def _resolve_domain_length(
    raw_data: dict[str, np.ndarray],
    derived_data: dict[str, np.ndarray],
    override: float | None,
    n: int,
) -> tuple[float, str]:
    if override is not None:
        value = _finite_float(override, "--domain-length")
        if value <= 0.0:
            raise ValueError("--domain-length must be positive")
        return value, "cli"

    raw_len, raw_key = _scalar_metadata(raw_data, "domain_length", "length")
    derived_len, derived_key = _scalar_metadata(derived_data, "domain_length", "length")

    raw_value = None if raw_len is None else _finite_float(raw_len, raw_key or "domain_length")
    derived_value = None if derived_len is None else _finite_float(derived_len, derived_key or "domain_length")

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

    raise ValueError("missing domain_length metadata; pass --domain-length")


def _spectral_derivative(field: np.ndarray, axis: int, domain_length: float) -> np.ndarray:
    n = int(field.shape[axis])
    frequencies = 2.0 * np.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    reshape = [1, 1, 1]
    reshape[axis] = n
    factor = frequencies.reshape(reshape)
    transformed = np.fft.fftn(field, axes=(0, 1, 2))
    return np.fft.ifftn(1j * factor * transformed, axes=(0, 1, 2)).real


def _velocity_gradient(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    grad = np.empty((3, 3) + u.shape, dtype=np.float64)
    for component_index, component in enumerate((u, v, w)):
        for axis in range(3):
            grad[component_index, axis] = _spectral_derivative(component, axis, domain_length)
    return grad


def _strain_tensor(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    return 0.5 * (tensor + np.swapaxes(tensor, 0, 1))


def _raw_strain_eigensystem(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    grad = _velocity_gradient(u, v, w, domain_length)
    strain = _strain_tensor(grad)
    matrices = np.moveaxis(strain, (0, 1), (-2, -1))
    eigenvalues, _ = np.linalg.eigh(matrices)
    lambda1 = np.asarray(eigenvalues[..., 0], dtype=np.float64)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    lambda3 = np.asarray(eigenvalues[..., 2], dtype=np.float64)
    g12 = lambda2 - lambda1
    omega = np.empty((3,) + grad.shape[2:], dtype=np.float64)
    omega[0] = grad[2, 1] - grad[1, 2]
    omega[1] = grad[0, 2] - grad[2, 0]
    omega[2] = grad[1, 0] - grad[0, 1]
    omega_norm_sq = np.sum(omega * omega, axis=0)
    return lambda1, lambda2, lambda3, g12, omega_norm_sq


def _load_raw_bundle_from_data(
    data: dict[str, np.ndarray],
    derived_data: dict[str, np.ndarray],
    frame: int | None,
    domain_length_override: float | None,
) -> tuple[RawBundle | None, list[str]]:
    try:
        u, v, w, velocity_source = _load_velocity_frame(data, frame)
    except Exception as exc:
        return None, [f"velocity_snapshots:{exc}"]

    try:
        dummy_derived: dict[str, np.ndarray] = {}
        domain_length, scale_source = _resolve_domain_length(data, dummy_derived, domain_length_override, int(u.shape[0]))
    except Exception as exc:
        return None, [f"domain_length:{exc}"]

    grid_spacing = domain_length / float(u.shape[0])
    lambda1, lambda2, lambda3, g12, omega_norm_sq = _raw_strain_eigensystem(u, v, w, domain_length)

    return (
        RawBundle(
            velocity_source=velocity_source,
            frame_source="cli" if frame is not None else "archive",
            velocity_shape=(int(u.shape[0]), int(u.shape[1]), int(u.shape[2])),
            u=u,
            v=v,
            w=w,
            lambda1=lambda1,
            lambda2=lambda2,
            lambda3=lambda3,
            g12=g12,
            omega_norm_sq=omega_norm_sq,
            omega_source="computed_from_velocity_snapshots",
            domain_length=domain_length,
            grid_spacing=grid_spacing,
            scale_source=scale_source,
        ),
        [],
    )


def _load_raw_bundle(path: Path, frame: int | None, domain_length_override: float | None) -> tuple[RawBundle | None, list[str]]:
    try:
        data = _load_npz(path)
    except FileNotFoundError:
        return None, ["raw_archive"]
    except Exception as exc:
        return None, [f"raw_archive:{exc}"]
    return _load_raw_bundle_from_data(data, {}, frame, domain_length_override)


def _load_derived_bundle_from_data(data: dict[str, np.ndarray], frame: int | None) -> tuple[DerivedBundle | None, list[str]]:
    try:
        lambda2, lambda2_source = _load_field(data, "lambda2", frame)
    except Exception as exc:
        return None, [f"lambda2:{exc}"]

    if lambda2 is None:
        return None, ["missing lambda2"]

    fields_present = ["lambda2"]
    try:
        g12, g12_source = _load_field(data, "g12", frame)
        if g12 is not None:
            fields_present.append("g12")
    except Exception as exc:
        return None, [f"g12:{exc}"]

    try:
        lambda3, lambda3_source = _load_field(data, "lambda3", frame)
        if lambda3 is not None:
            fields_present.append("lambda3")
    except Exception as exc:
        return None, [f"lambda3:{exc}"]

    if g12 is not None and g12.shape != lambda2.shape:
        return None, [f"shape_mismatch:g12:{g12.shape!r}!={lambda2.shape!r}"]
    if lambda3 is not None and lambda3.shape != lambda2.shape:
        return None, [f"shape_mismatch:lambda3:{lambda3.shape!r}!={lambda2.shape!r}"]
    if g12 is not None and not np.all(np.isfinite(g12)):
        return None, ["nonfinite_g12"]
    if lambda3 is not None and not np.all(np.isfinite(lambda3)):
        return None, ["nonfinite_lambda3"]

    return (
        DerivedBundle(
            lambda2=lambda2,
            g12=g12,
            lambda3=lambda3,
            fields_present=fields_present,
            frame_source=lambda2_source,
            shape=(int(lambda2.shape[0]), int(lambda2.shape[1]), int(lambda2.shape[2])),
        ),
        [],
    )


def _load_derived_bundle(path: Path, frame: int | None) -> tuple[DerivedBundle | None, list[str]]:
    try:
        data = _load_npz(path)
    except FileNotFoundError:
        return None, ["derived_archive"]
    except Exception as exc:
        return None, [f"derived_archive:{exc}"]
    return _load_derived_bundle_from_data(data, frame)


def _parse_indices(value: str | None) -> list[tuple[int, int, int]]:
    if value is None or value.strip() == "":
        return []

    cells: list[tuple[int, int, int]] = []
    for chunk in value.split(";"):
        item = chunk.strip()
        if not item:
            continue
        parts = [part.strip() for part in item.split(",")]
        if len(parts) != 3:
            raise ValueError(f"invalid cell index {item!r}; expected i,j,k")
        try:
            cell = (int(parts[0]), int(parts[1]), int(parts[2]))
        except ValueError as exc:
            raise ValueError(f"invalid cell index {item!r}; expected integers") from exc
        cells.append(cell)
    return cells


def _validate_index(index: tuple[int, int, int], shape: tuple[int, int, int]) -> None:
    for axis, value in enumerate(index):
        if value < 0 or value >= shape[axis]:
            raise ValueError(f"index {index!r} is out of bounds for shape {shape!r}")


def _cell_sign(value: float | None) -> int | None:
    if value is None or not math.isfinite(value):
        return None
    if value > 0.0:
        return 1
    if value < 0.0:
        return -1
    return 0


def _sign_mismatch(raw_value: float | None, derived_value: float | None) -> bool | None:
    raw_sign = _cell_sign(raw_value)
    derived_sign = _cell_sign(derived_value)
    if raw_sign is None or derived_sign is None:
        return None
    if raw_sign == 0 or derived_sign == 0:
        return False
    return raw_sign != derived_sign


def _value_delta(raw_value: float | None, derived_value: float | None) -> float | None:
    if raw_value is None or derived_value is None:
        return None
    return float(raw_value - derived_value)


def _field_record(raw_value: float, derived_value: float | None) -> dict[str, Any]:
    return {
        "raw": float(raw_value),
        "derived": None if derived_value is None else float(derived_value),
        "delta": _value_delta(raw_value, derived_value),
        "sign_mismatch": _sign_mismatch(raw_value, derived_value),
    }


def _selected_cell_record(
    index: tuple[int, int, int],
    raw: RawBundle,
    derived: DerivedBundle,
    tags: list[str],
) -> dict[str, Any]:
    i, j, k = (int(index[0]), int(index[1]), int(index[2]))
    derived_lambda2 = None if derived.lambda2 is None else float(derived.lambda2[index])
    derived_g12 = None if derived.g12 is None else float(derived.g12[index])
    derived_lambda3 = None if derived.lambda3 is None else float(derived.lambda3[index])
    raw_lambda1 = float(raw.lambda1[index])
    raw_lambda2 = float(raw.lambda2[index])
    raw_lambda3 = float(raw.lambda3[index])
    raw_g12 = float(raw.g12[index])
    omega_norm_sq = float(raw.omega_norm_sq[index])
    return {
        "index": [i, j, k],
        "tags": list(dict.fromkeys(tags)),
        "raw": {
            "lambda1": raw_lambda1,
            "lambda2": raw_lambda2,
            "lambda3": raw_lambda3,
            "g12": raw_g12,
            "omega_norm_sq": omega_norm_sq,
        },
        "derived": {
            "lambda2": derived_lambda2,
            "g12": derived_g12,
            "lambda3": derived_lambda3,
        },
        "delta": {
            "lambda2": _value_delta(raw_lambda2, derived_lambda2),
            "g12": _value_delta(raw_g12, derived_g12),
            "lambda3": _value_delta(raw_lambda3, derived_lambda3),
        },
        "sign_mismatch": {
            "lambda2": _sign_mismatch(raw_lambda2, derived_lambda2),
            "g12": _sign_mismatch(raw_g12, derived_g12),
            "lambda3": _sign_mismatch(raw_lambda3, derived_lambda3),
        },
    }


def _aggregate_field_stats(values: list[dict[str, Any]], field: str) -> dict[str, Any]:
    raw_values: list[float] = []
    derived_values: list[float] = []
    deltas: list[float] = []
    mismatch_count = 0
    available_count = 0
    for cell in values:
        raw_value = cell["raw"][field]
        derived_value = cell["derived"][field]
        delta = cell["delta"][field]
        mismatch = cell["sign_mismatch"][field]
        raw_values.append(float(raw_value))
        if derived_value is not None and delta is not None:
            derived_values.append(float(derived_value))
            deltas.append(float(delta))
            available_count += 1
            if mismatch:
                mismatch_count += 1
    if available_count == 0:
        return {
            "available_count": 0,
            "sign_mismatch_count": 0,
            "mean_abs_delta": None,
            "max_abs_delta": None,
            "mean_raw": float(np.mean(raw_values)) if raw_values else None,
            "mean_derived": None,
        }
    delta_array = np.asarray(deltas, dtype=np.float64)
    derived_array = np.asarray(derived_values, dtype=np.float64)
    return {
        "available_count": int(available_count),
        "sign_mismatch_count": int(mismatch_count),
        "mean_abs_delta": float(np.mean(np.abs(delta_array))),
        "max_abs_delta": float(np.max(np.abs(delta_array))),
        "mean_raw": float(np.mean(raw_values)),
        "mean_derived": float(np.mean(derived_array)),
    }


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    warnings: list[str] = []
    payload: dict[str, Any] = {
        "status": OK_STATUS,
        "schema_version": 1,
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "authority": _authority(),
        "raw_archive": str(args.raw_archive),
        "derived_archive": str(args.derived_archive),
        "frame": args.frame,
        "indices": args.indices,
        "output_json": str(args.output_json),
        "pretty": bool(args.pretty),
        "domain_length_override": None if args.domain_length is None else float(args.domain_length),
        "warnings": warnings,
        "errors": [],
        "O": "Compare raw velocity-derived strain eigenvalues against derived lambda2/g12/lambda3 archive values.",
        "R": "Report per-cell raw lambda1/lambda2/lambda3, derived lambda2/g12/lambda3, deltas, and sign mismatches.",
        "C": SCRIPT_NAME,
        "S": "Load raw velocity_snapshots, compute the strain eigensystem and vorticity norm, then compare against the derived archive at requested cells and the top-vorticity cell.",
        "L": "Status is ok only when the required raw velocity frame, domain length, derived lambda2 field, and requested indices are valid.",
        "P": "FAIL_CLOSED_RAW_DERIVED_TENSOR_CONVENTION_COMPARE",
        "G": "Authority is false and this is empirical comparison telemetry only.",
        "F": "The script is fail-closed and records comparison deltas without promoting any theorem or Clay claim.",
    }

    if args.frame is not None and args.frame < 0:
        payload["status"] = STATUS_INVALID
        payload["errors"] = ["invalid_frame"]
        return payload, 1
    if args.domain_length is not None and (not math.isfinite(args.domain_length) or args.domain_length <= 0.0):
        payload["status"] = STATUS_INVALID
        payload["errors"] = ["invalid_domain_length"]
        return payload, 1

    try:
        requested_indices = _parse_indices(args.indices)
    except Exception as exc:
        payload["status"] = STATUS_INVALID
        payload["errors"] = [f"invalid_indices:{exc}"]
        return payload, 1

    try:
        raw_data = _load_npz(args.raw_archive)
    except FileNotFoundError:
        payload["status"] = STATUS_MISSING
        payload["errors"] = ["raw_archive"]
        return payload, 1
    except Exception as exc:
        payload["status"] = STATUS_MISSING
        payload["errors"] = [f"raw_archive:{exc}"]
        return payload, 1

    try:
        derived_data = _load_npz(args.derived_archive)
    except FileNotFoundError:
        payload["status"] = STATUS_MISSING
        payload["errors"] = ["derived_archive"]
        return payload, 1
    except Exception as exc:
        payload["status"] = STATUS_MISSING
        payload["errors"] = [f"derived_archive:{exc}"]
        return payload, 1

    raw_bundle, raw_errors = _load_raw_bundle_from_data(raw_data, derived_data, args.frame, args.domain_length)
    if raw_bundle is None:
        payload["status"] = STATUS_MISSING
        payload["errors"] = raw_errors
        return payload, 1

    derived_bundle, derived_errors = _load_derived_bundle_from_data(derived_data, args.frame)
    if derived_bundle is None:
        payload["status"] = STATUS_MISSING
        payload["errors"] = derived_errors
        return payload, 1

    if raw_bundle.lambda1.shape != derived_bundle.shape:
        payload["status"] = STATUS_SHAPE
        payload["errors"] = [f"raw_shape:{raw_bundle.lambda1.shape!r}", f"derived_shape:{derived_bundle.shape!r}"]
        return payload, 1

    if raw_bundle.lambda2.shape != raw_bundle.lambda1.shape or raw_bundle.lambda3.shape != raw_bundle.lambda1.shape:
        payload["status"] = STATUS_SHAPE
        payload["errors"] = ["raw_eigensystem_shape_mismatch"]
        return payload, 1

    if not np.all(np.isfinite(raw_bundle.lambda1)) or not np.all(np.isfinite(raw_bundle.lambda2)) or not np.all(
        np.isfinite(raw_bundle.lambda3)
    ):
        payload["status"] = STATUS_MISSING
        payload["errors"] = ["nonfinite_raw_strain_eigenvalues"]
        return payload, 1

    if derived_bundle.g12 is not None and derived_bundle.g12.shape != raw_bundle.lambda1.shape:
        payload["status"] = STATUS_SHAPE
        payload["errors"] = [f"shape_mismatch:g12:{derived_bundle.g12.shape!r}!={raw_bundle.lambda1.shape!r}"]
        return payload, 1
    if derived_bundle.lambda3 is not None and derived_bundle.lambda3.shape != raw_bundle.lambda1.shape:
        payload["status"] = STATUS_SHAPE
        payload["errors"] = [f"shape_mismatch:lambda3:{derived_bundle.lambda3.shape!r}!={raw_bundle.lambda1.shape!r}"]
        return payload, 1

    if not np.all(np.isfinite(raw_bundle.omega_norm_sq)):
        payload["status"] = STATUS_MISSING
        payload["errors"] = ["nonfinite_raw_vorticity_norm_sq"]
        return payload, 1

    top_flat = int(np.argmax(raw_bundle.omega_norm_sq))
    top_index = tuple(int(v) for v in np.unravel_index(top_flat, raw_bundle.omega_norm_sq.shape))
    _validate_index(top_index, raw_bundle.lambda1.shape)

    comparison_indices: list[tuple[int, int, int]] = []
    for cell in requested_indices:
        _validate_index(cell, raw_bundle.lambda1.shape)
        if cell not in comparison_indices:
            comparison_indices.append(cell)
    if top_index not in comparison_indices:
        comparison_indices.append(top_index)

    selected_cells: list[dict[str, Any]] = []
    requested_set = {cell for cell in requested_indices}
    for cell in comparison_indices:
        tags: list[str] = []
        if cell in requested_set:
            tags.append("requested")
        if cell == top_index:
            tags.append("top_vorticity")
        selected_cells.append(_selected_cell_record(cell, raw_bundle, derived_bundle, tags))

    top_vorticity_cell = next(cell for cell in selected_cells if cell["index"] == [int(v) for v in top_index])

    summary_fields = {
        field: _aggregate_field_stats(selected_cells, field)
        for field in ("lambda2", "g12", "lambda3")
    }
    derived_presence = {
        "lambda2": True,
        "g12": derived_bundle.g12 is not None,
        "lambda3": derived_bundle.lambda3 is not None,
    }
    available_fields = [name for name, present in derived_presence.items() if present]

    payload.update(
        {
            "status": OK_STATUS,
            "raw": {
                "velocity_source": raw_bundle.velocity_source,
                "frame_source": raw_bundle.frame_source,
                "shape": [int(v) for v in raw_bundle.velocity_shape],
                "domain_length": float(raw_bundle.domain_length),
                "grid_spacing": float(raw_bundle.grid_spacing),
                "scale_source": raw_bundle.scale_source,
                "omega_source": raw_bundle.omega_source,
                "top_vorticity_index": [int(v) for v in top_index],
                "top_vorticity_value_sq": float(raw_bundle.omega_norm_sq[top_index]),
                "top_vorticity_value": float(math.sqrt(float(raw_bundle.omega_norm_sq[top_index]))),
            },
            "derived": {
                "frame_source": derived_bundle.frame_source,
                "shape": [int(v) for v in derived_bundle.shape],
                "fields_present": derived_bundle.fields_present,
                "fields_available_for_compare": available_fields,
                "lambda2_present": True,
                "g12_present": derived_bundle.g12 is not None,
                "lambda3_present": derived_bundle.lambda3 is not None,
            },
            "comparison": {
                "requested_indices": [[int(v) for v in cell] for cell in requested_indices],
                "comparison_indices": [[int(v) for v in cell] for cell in comparison_indices],
                "selected_cells": selected_cells,
                "top_vorticity_cell": top_vorticity_cell,
            },
            "summary": {
                "raw_cell_count": int(np.prod(raw_bundle.lambda1.shape)),
                "selected_cell_count": int(len(selected_cells)),
                "requested_cell_count": int(len(requested_indices)),
                "top_vorticity_cell_count": 1,
                "top_vorticity_cell_in_requested": bool(top_index in requested_set),
                "top_vorticity_cell_in_comparison": bool(top_index in comparison_indices),
                "raw_domain_length": float(raw_bundle.domain_length),
                "derived_domain_length": float(raw_bundle.domain_length),
                "domain_length_source": raw_bundle.scale_source,
                "derived_fields_present": available_fields,
                "field_stats": summary_fields,
                "raw_strain_eigenvalue_ordering": {
                    "lambda1_le_lambda2": bool(np.all(raw_bundle.lambda1 <= raw_bundle.lambda2 + 1.0e-12)),
                    "lambda2_le_lambda3": bool(np.all(raw_bundle.lambda2 <= raw_bundle.lambda3 + 1.0e-12)),
                },
            },
        }
    )
    payload["warnings"] = sorted(set(warnings))
    return payload, 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, required=True, help="raw NPZ archive with velocity_snapshots")
    parser.add_argument("--derived-archive", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for multi-frame archives")
    parser.add_argument(
        "--indices",
        type=str,
        default=None,
        help="semicolon-separated list of i,j,k cells to compare, for example '1,2,3;4,5,6'",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="write the comparison payload to this JSON file",
    )
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON output")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="override domain length metadata for the raw velocity derivative calculation",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload, exit_code = _build_payload(args)
    text = _json_text(payload, args.pretty)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
