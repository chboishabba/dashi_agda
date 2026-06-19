#!/usr/bin/env python3
"""Emit per-frame omega L3 diagnostics from raw vorticity snapshots.

The runner reads a raw ``.npz`` archive containing ``omega_snapshots`` and emits a
deterministic JSON report with per-frame diagnostics:

* ``L3`` norm over the periodic cube
* ``Linf`` norm
* ``L2`` norm (and a matching enstrophy proxy)
* mean and max-index metadata

Domain length is inferred from metadata where possible, can be set with
``--domain-length``, or falls back to ``2*pi``. Integral estimates are produced
via coordinate ``trapz`` when full 1D axis arrays are available; otherwise
uniform-cell ``sum`` estimates are used.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_omega_l3_timeseries_diagnostic.py"
CONTRACT = "ns_omega_l3_timeseries_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_OMEGA_L3_TIMESERIES_DIAGNOSTIC"
OK_STATUS = "ok"
ERROR_STATUS = "error"
DEFAULT_OUTPUT = Path("outputs/ns_omega_l3_timeseries_diagnostic.json")
DEFAULT_DOMAIN_LENGTH = 2.0 * math.pi


def _finite_float(value: Any, *, field: str) -> float:
    try:
        parsed = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{field} must be a finite float") from exc
    if not math.isfinite(parsed):
        raise ValueError(f"{field} must be finite")
    return float(parsed)


def _coerce_scalar_like(value: Any, field: str) -> float:
    if isinstance(value, np.ndarray):
        arr = np.asarray(value)
        if arr.ndim == 0:
            value = arr.item()
        elif arr.ndim == 1 and arr.size == 1:
            value = arr.reshape(()).item()
        else:
            raise ValueError(f"{field} must be scalar, got shape {arr.shape!r}")

    if isinstance(value, bytes):
        value = value.decode("utf-8")
    if isinstance(value, str):
        return _finite_float(value.strip(), field=field)
    if isinstance(value, (list, tuple)):
        if len(value) != 1:
            raise ValueError(f"{field} must be scalar, got len={len(value)}")
        value = value[0]
    if isinstance(value, bool) or value is None:
        raise ValueError(f"{field} must be numeric, got {type(value).__name__}")
    return _finite_float(value, field=field)


def _coerce_vector(value: Any, field: str) -> list[float] | None:
    if value is None:
        return None

    if isinstance(value, np.ndarray):
        arr = np.asarray(value, dtype=np.float64)
        if arr.ndim == 0:
            return None
        arr = arr.reshape(-1)
        if arr.size == 0:
            return []
        if not np.all(np.isfinite(arr)):
            raise ValueError(f"{field} contains non-finite values")
        return [float(v) for v in arr]

    if isinstance(value, (list, tuple)):
        arr = np.asarray(value, dtype=np.float64).reshape(-1)
        if arr.size == 0:
            return []
        if not np.all(np.isfinite(arr)):
            raise ValueError(f"{field} contains non-finite values")
        return [float(v) for v in arr]

    if isinstance(value, bytes):
        value = value.decode("utf-8")
    if isinstance(value, str):
        try:
            parsed = json.loads(value)
        except json.JSONDecodeError as exc:
            raise ValueError(f"{field} must be a numeric vector or parseable JSON vector") from exc
        return _coerce_vector(parsed, field)

    return None


def _coerce_time_vector(value: Any, expected: int | None, field: str) -> list[float] | None:
    vector = _coerce_vector(value, field)
    if vector is None:
        return None
    if expected is not None and len(vector) not in (0, expected):
        raise ValueError(f"{field} length {len(vector)} does not match frame_count {expected}")
    return [float(v) for v in vector]


def _find_metadata_value(data: dict[str, Any], metadata: dict[str, Any], keys: tuple[str, ...]) -> Any | None:
    for key in keys:
        if key in data:
            return data[key]
        if key in metadata:
            return metadata[key]
    return None


def _load_npz(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}

    metadata: dict[str, Any] = {}
    if "meta_json" in payload:
        raw_meta = payload["meta_json"]
        try:
            if isinstance(raw_meta, np.ndarray) and raw_meta.shape == ():
                raw_meta = raw_meta.item()
            if isinstance(raw_meta, bytes):
                raw_meta = raw_meta.decode("utf-8")
            if isinstance(raw_meta, str):
                parsed_meta = json.loads(raw_meta)
            else:
                parsed_meta = raw_meta
            if isinstance(parsed_meta, dict):
                metadata = {str(key): value for key, value in parsed_meta.items()}
        except Exception:
            # Optional metadata path: fail only if required fields are genuinely absent.
            pass

    return payload, metadata


def _select_axis(values: dict[str, Any], metadata: dict[str, Any], axis: str) -> np.ndarray | None:
    candidates = {
        "x": ("x", "x_grid", "x_coords", "grid_x", "xs"),
        "y": ("y", "y_grid", "y_coords", "grid_y", "ys"),
        "z": ("z", "z_grid", "z_coords", "grid_z", "zs"),
    }[axis]

    for key in candidates:
        value = _find_metadata_value(values, metadata, (key,))
        if value is None:
            continue
        vector = _coerce_vector(value, axis)
        if vector is None:
            continue
        if len(vector) <= 1:
            continue
        arr = np.asarray(vector, dtype=np.float64)
        if not np.all(np.isfinite(arr)):
            continue
        if arr.ndim == 1:
            return arr
    return None


def _extract_omega_layout(raw: np.ndarray) -> tuple[str, int]:
    if raw.ndim == 3:
        return "scalar", 1

    if raw.ndim == 4:
        if raw.shape[-1] == 3 and raw.shape[0] != 3:
            return "vector_last", int(raw.shape[0])
        if raw.shape[0] == 3 and raw.shape[-1] != 3:
            return "vector_first", 1
        return "scalar_frames", int(raw.shape[0])

    if raw.ndim == 5:
        if raw.shape[1] == 3:
            return "vector_channel_second", int(raw.shape[0])
        if raw.shape[-1] == 3:
            return "vector_last", int(raw.shape[0])

    raise ValueError(
        f"unsupported omega_snapshots rank {raw.ndim}; expected 3D scalar, 4D, or 5D tensor"
    )


def _omega_snapshot(raw: np.ndarray, layout: str, frame_index: int) -> np.ndarray:
    if layout == "scalar":
        return np.asarray(raw, dtype=np.float64)
    if layout == "scalar_frames":
        return np.asarray(raw[frame_index], dtype=np.float64)
    if layout == "vector_last":
        snapshot = np.asarray(raw[frame_index], dtype=np.float64)
        if snapshot.ndim != 4:
            raise ValueError("vector_last layout must be per-frame with 3 components")
        return np.sqrt(np.sum(snapshot**2, axis=-1, dtype=np.float64))
    if layout == "vector_first":
        snapshot = np.asarray(raw, dtype=np.float64)
        if snapshot.shape[0] != 3:
            raise ValueError("vector_first layout must be (3, N, N, N)")
        return np.sqrt(np.sum(snapshot**2, axis=0, dtype=np.float64))
    if layout == "vector_channel_second":
        snapshot = np.asarray(raw[frame_index], dtype=np.float64)
        if snapshot.ndim != 4 or snapshot.shape[0] != 3:
            raise ValueError("vector_channel_second layout must be (3, N, N, N) per frame")
        return np.sqrt(np.sum(snapshot**2, axis=0, dtype=np.float64))
    raise ValueError(f"unknown omega layout {layout!r}")


def _integral_sum(values: np.ndarray, cell_volume: float) -> float:
    return float(np.sum(values, dtype=np.float64) * cell_volume)


def _integral_trapz(values: np.ndarray, x: np.ndarray, y: np.ndarray, z: np.ndarray) -> float:
    tmp = np.trapz(values, x=z, axis=2)
    tmp = np.trapz(tmp, x=y, axis=1)
    return float(np.trapz(tmp, x=x, axis=0))


def _volume_from_axes(x: np.ndarray, y: np.ndarray, z: np.ndarray) -> float:
    return float(x[-1] - x[0]) * float(y[-1] - y[0]) * float(z[-1] - z[0])


def _build_rows(
    omega_raw: np.ndarray,
    frame_count: int,
    layout: str,
    volume: float,
    cell_volume: float | None,
    use_trapz: bool,
    x_axis: np.ndarray | None,
    y_axis: np.ndarray | None,
    z_axis: np.ndarray | None,
    times: list[float] | None,
) -> tuple[list[dict[str, Any]], list[str], bool]:
    rows: list[dict[str, Any]] = []
    warnings: list[str] = []
    frame_invalid = False

    for frame in range(frame_count):
        row: dict[str, Any] = {"frame": frame, "status": OK_STATUS}
        if times is not None:
            row["time"] = times[frame]

        try:
            omega_mag = _omega_snapshot(omega_raw, layout, frame)
        except Exception as exc:
            row["status"] = ERROR_STATUS
            row["errors"] = [f"snapshot_load:{exc}"]
            frame_invalid = True
            rows.append(row)
            continue

        omega_mag = np.abs(np.asarray(omega_mag, dtype=np.float64))
        finite = np.isfinite(omega_mag)
        if finite.size == 0 or not finite.any():
            row["status"] = ERROR_STATUS
            row["errors"] = ["no_finite_cells"]
            frame_invalid = True
            rows.append(row)
            continue

        if not np.all(finite):
            warnings.append("nonfinite_omega_cells")
        omega_finite = omega_mag[finite]
        max_finite_index = int(np.argmax(omega_finite))
        max_index = np.array(np.argwhere(finite))[max_finite_index]

        if use_trapz:
            if x_axis is None or y_axis is None or z_axis is None:
                raise RuntimeError("trapz requested but one axis is missing")
            omega_l2_integral = _integral_trapz(omega_mag * omega_mag, x_axis, y_axis, z_axis)
            omega_l3_integral = _integral_trapz(omega_mag * omega_mag * omega_mag, x_axis, y_axis, z_axis)
            integral_notes = ["trapz", "axes=explicit"]
        else:
            if cell_volume is None:
                raise RuntimeError("sum integration requested without cell volume")
            omega_l2_integral = _integral_sum(omega_mag * omega_mag, cell_volume)
            omega_l3_integral = _integral_sum(omega_mag * omega_mag * omega_mag, cell_volume)
            integral_notes = ["sum", f"cell_volume={cell_volume:.6g}"]

        omega_l2_sq_mean = omega_l2_integral / volume
        omega_l3_cube_mean = omega_l3_integral / volume
        omega_l3_domain_norm = float(omega_l3_integral ** (1.0 / 3.0))
        if omega_l2_sq_mean < 0.0:
            if omega_l2_sq_mean < -1.0e-15:
                row["status"] = ERROR_STATUS
                row["errors"] = ["negative_l2_mean_square"]
                frame_invalid = True
                rows.append(row)
                continue
            omega_l2_sq_mean = 0.0

        if omega_l3_cube_mean < 0.0:
            row["status"] = ERROR_STATUS
            row["errors"] = ["negative_l3_mean_cube"]
            frame_invalid = True
            rows.append(row)
            continue

        row.update(
            {
                "omega_l3_norm": float(omega_l3_cube_mean ** (1.0 / 3.0)),
                "omega_l3_domain_norm": omega_l3_domain_norm,
                "omega_linf": float(np.max(omega_finite)),
                "omega_l2_norm": float(math.sqrt(omega_l2_sq_mean)),
                "mean": float(np.mean(omega_finite)),
                "omega_l2_sq_domain_integral": float(omega_l2_integral),
                "omega_l3_domain_integral": float(omega_l3_integral),
                "enstrophy_proxy": float(0.5 * omega_l2_integral),
                "max_index": [int(max_index[0]), int(max_index[1]), int(max_index[2])],
                "max_value": float(np.max(omega_finite)),
                "finite_cell_count": int(omega_finite.size),
                "total_cell_count": int(omega_mag.size),
                "integration_notes": integral_notes,
            }
        )
        rows.append(row)

    return rows, sorted(set(warnings)), frame_invalid


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    output = args.output_json
    payload: dict[str, Any] = {
        "schema_version": "1.0.0",
        "contract": CONTRACT,
        "script": SCRIPT_NAME,
        "route_decision": ROUTE_DECISION,
        "input": str(args.input),
        "output": str(output),
        "O": "Emit a deterministic per-frame periodic-domain omega diagnostics report from raw snapshots.",
        "R": "Load raw omega_snapshots and compute L3, Linf, L2/enstrophy-proxy, mean, and max-index stats.",
        "C": SCRIPT_NAME,
        "S": "Validate input shape/metadata and fail-closed on malformed archives or non-finite per-frame data.",
        "L": "Status is ok only if required fields and all frame computations are finite.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or runtime authority is claimed by this diagnostic.",
        "F": "Fail-closed empirical diagnostic; authority flags remain false.",
        "authority": {
            "candidate_only": False,
            "empirical_non_promoting": False,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        "status": OK_STATUS,
        "warnings": [],
        "errors": [],
        "changed_paths": [str(output)],
    }

    try:
        data, metadata = _load_npz(args.input)
    except OSError as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"input_load:{exc}"]
        return payload, 1
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"input_read:{exc}"]
        return payload, 1

    if "omega_snapshots" not in data:
        payload["status"] = ERROR_STATUS
        payload["errors"] = ["missing_required_field:omega_snapshots"]
        return payload, 1

    omega_raw = np.asarray(data["omega_snapshots"], dtype=np.float64)
    if omega_raw.ndim not in (3, 4, 5):
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"unsupported_omega_ndim:{omega_raw.ndim}"]
        return payload, 1

    try:
        layout, frame_count = _extract_omega_layout(omega_raw)
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"omega_layout:{exc}"]
        return payload, 1

    if layout == "scalar":
        grid_shape = omega_raw.shape
    elif layout == "scalar_frames":
        grid_shape = omega_raw.shape[1:]
    else:
        grid_shape = omega_raw.shape[1:4]

    if len(grid_shape) != 3:
        payload["status"] = ERROR_STATUS
        payload["errors"] = ["unsupported_grid_shape"]
        return payload, 1
    if any(axis <= 0 for axis in grid_shape):
        payload["status"] = ERROR_STATUS
        payload["errors"] = ["invalid_grid_shape"]
        return payload, 1

    n = int(grid_shape[0])
    if grid_shape[0] != grid_shape[1] or grid_shape[1] != grid_shape[2]:
        payload["warnings"].append("non_cubic_grid")

    x_axis = _select_axis(data, metadata, "x")
    y_axis = _select_axis(data, metadata, "y")
    z_axis = _select_axis(data, metadata, "z")

    use_trapz = x_axis is not None and y_axis is not None and z_axis is not None
    if use_trapz:
        if not (len(x_axis) == len(y_axis) == len(z_axis) == n):
            payload["warnings"].append("axis_length_mismatch_fallback_to_sum")
            use_trapz = False

    if use_trapz:
        volume = _volume_from_axes(x_axis, y_axis, z_axis)  # type: ignore[arg-type]
        if not math.isfinite(volume) or volume <= 0.0:
            payload["status"] = ERROR_STATUS
            payload["errors"] = ["invalid_trapz_volume"]
            return payload, 1
        payload["integration_method"] = "trapz"
        payload["domain_length"] = float(volume ** (1.0 / 3.0))
        payload["axis_coordinate_count"] = n
    else:
        domain_length = args.domain_length
        if domain_length is None:
            metadata_domain = _find_metadata_value(
                data,
                metadata,
                ("domain_length", "length", "L", "domain_size"),
            )
            if metadata_domain is not None:
                try:
                    domain_length = _coerce_scalar_like(metadata_domain, "domain_length")
                    payload["domain_length_source"] = "metadata"
                except Exception:
                    payload["warnings"].append("invalid_metadata_domain_length")
            if domain_length is None:
                metadata_spacing = _find_metadata_value(data, metadata, ("grid_spacing", "dx", "dx_grid"))
                if metadata_spacing is not None:
                    try:
                        grid_spacing = _coerce_scalar_like(metadata_spacing, "grid_spacing")
                        if grid_spacing > 0.0:
                            domain_length = grid_spacing * n
                            payload["domain_length_source"] = "grid_spacing"
                            payload["grid_spacing"] = float(grid_spacing)
                    except Exception:
                        payload["warnings"].append("invalid_metadata_grid_spacing")
            if domain_length is None:
                domain_length = DEFAULT_DOMAIN_LENGTH
                payload["domain_length_source"] = "default"

        if domain_length <= 0.0:
            payload["status"] = ERROR_STATUS
            payload["errors"] = ["invalid_domain_length"]
            return payload, 1
        volume = float(domain_length) ** 3
        payload["integration_method"] = "sum"
        payload["domain_length"] = float(domain_length)
        payload["cell_volume"] = float(volume / (float(n) ** 3))

    payload["frame_count"] = int(frame_count)

    dt = _find_metadata_value(data, metadata, ("dt", "delta_t", "time_step"))
    if dt is not None:
        try:
            payload["dt"] = _coerce_scalar_like(dt, "dt")
        except Exception as exc:
            payload["warnings"].append(f"invalid_dt:{exc}")

    times = _find_metadata_value(data, metadata, ("time", "times", "t", "snapshot_time", "snapshot_times"))
    try:
        parsed_time = _coerce_time_vector(times, frame_count, "time")
    except Exception as exc:
        parsed_time = None
        payload["warnings"].append(f"invalid_time:{exc}")

    if parsed_time is None:
        steps = _find_metadata_value(data, metadata, ("steps", "step", "snapshot_index"))
        try:
            parsed_steps = _coerce_time_vector(steps, frame_count, "steps")
            if parsed_steps is not None:
                payload["steps"] = parsed_steps
                parsed_time = parsed_steps
        except Exception as exc:
            payload["warnings"].append(f"invalid_steps:{exc}")

    if parsed_time is not None:
        payload["time"] = parsed_time

    rows, warnings, invalid = _build_rows(
        omega_raw=omega_raw,
        frame_count=frame_count,
        layout=layout,
        volume=volume,
        cell_volume=payload.get("cell_volume", None),
        use_trapz=use_trapz,
        x_axis=x_axis,
        y_axis=y_axis,
        z_axis=z_axis,
        times=parsed_time,
    )

    payload["rows"] = rows
    payload["integration_notes"] = ["trapz" if use_trapz else "sum"]
    payload["warnings"].extend(warnings)
    payload["warnings"] = sorted(set(payload["warnings"]))
    if invalid:
        payload["status"] = ERROR_STATUS
        payload["errors"].append("one_or_more_frames_invalid")
        return payload, 1
    return payload, 0


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        required=True,
        help="Path to raw NPZ containing omega_snapshots.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output JSON.")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="Optional cubic domain side length. Defaults from metadata or 2*pi.",
    )
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def main() -> int:
    args = _parse_args()
    payload, code = _build_payload(args)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        _json_text(payload, args.pretty) + ("\n" if args.pretty else ""),
        encoding="utf-8",
    )
    return code


if __name__ == "__main__":
    raise SystemExit(main())
