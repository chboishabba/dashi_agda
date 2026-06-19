#!/usr/bin/env python3
"""Per-frame interior vorticity budget diagnostic for raw NS archives."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_interior_budget_timeseries_diagnostic.py"
CONTRACT = "ns_interior_budget_timeseries_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_NS_INTERIOR_BUDGET_TIMESERIES_DIAGNOSTIC"
DEFAULT_OUTPUT = Path("outputs/ns_interior_budget_timeseries_diagnostic.json")
DEFAULT_DOMAIN_LENGTH = 2.0 * math.pi
OK_STATUS = "ok"
ERROR_STATUS = "error"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        required=True,
        help="Raw NPZ archive with velocity_snapshots, omega_snapshots, and optional pressure_snapshots",
    )
    parser.add_argument(
        "--frames",
        type=str,
        default="all",
        help="Comma-separated frame list or inclusive ranges such as 0,3,5-8. Defaults to all frames.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="JSON output path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=DEFAULT_DOMAIN_LENGTH,
        help="Domain side length for spectral derivatives and omega norms",
    )
    return parser.parse_args()


def _authority_false_flags() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }


def _control_card() -> dict[str, str]:
    return {
        "O": "Emit per-frame worst-vorticity interior budget rows from a raw NS archive.",
        "R": "For each selected frame, locate the max-|omega| cell and compute spectral gradient eigendata, budget terms, pressure Laplacian, and omega L3 domain norm.",
        "C": "Deterministic numerical diagnostic from raw NPZ snapshots.",
        "S": "Fail closed on malformed archives, invalid frame selectors, non-finite values, and shape mismatches.",
        "L": "status=ok only when all requested frames are processed successfully and all required fields are finite.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or promotion authority is claimed.",
        "F": "Empirical finite-archive telemetry only; authority flags remain false.",
    }


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {name: np.asarray(data[name]) for name in data.files}


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return float(parsed)


def _validate_cubic(array: np.ndarray, name: str) -> int:
    if array.ndim != 3:
        raise ValueError(f"{name} must be 3D after frame extraction, got {array.shape!r}")
    n = int(array.shape[0])
    if int(array.shape[1]) != n or int(array.shape[2]) != n:
        raise ValueError(f"{name} must be cubic, got {array.shape!r}")
    if n <= 1:
        raise ValueError(f"{name} must have size > 1, got {n}")
    return n


def _select_scalar_snapshot(name: str, raw: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(raw, dtype=np.float64)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) == 1:
                arr = arr[0]
            else:
                raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frames")
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be 3D after frame selection, got {arr.shape!r}")
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} contains non-finite values")
    return arr


def _select_vector_snapshot(name: str, raw: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(raw, dtype=np.float64)

    if arr.ndim == 5:
        if arr.shape[-1] == 3:
            if frame is None:
                if int(arr.shape[0]) != 1:
                    raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frames")
                arr = arr[0]
            else:
                if frame < 0 or frame >= int(arr.shape[0]):
                    raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)")
                arr = arr[frame]
            comps = np.moveaxis(arr, -1, 0)
        elif arr.shape[1] == 3:
            if frame is None:
                if int(arr.shape[0]) != 1:
                    raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frames")
                comps = arr[0]
            else:
                if frame < 0 or frame >= int(arr.shape[0]):
                    raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)")
                comps = arr[frame]
        else:
            raise ValueError(f"{name} expected 3-vector channels on axis 1 or -1, got {arr.shape!r}")
    elif arr.ndim == 4:
        if arr.shape[-1] == 3:
            if frame is None:
                if arr.shape[0] == arr.shape[1] == arr.shape[2]:
                    arr = arr
                elif int(arr.shape[0]) == 1:
                    arr = arr[0]
                else:
                    raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frames")
            else:
                if frame < 0 or frame >= int(arr.shape[0]):
                    raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)")
                arr = arr[frame]
            comps = np.moveaxis(arr, -1, 0)
        elif arr.shape[0] == 3 and arr.shape[-1] != 3:
            if frame is not None:
                raise ValueError(f"{name} has no frame axis; omit --frames")
            comps = arr
        else:
            raise ValueError(f"{name} expected 3-vector channels on axis 0 or -1, got {arr.shape!r}")
    elif arr.ndim == 3:
        if arr.shape[0] != 3:
            raise ValueError(f"{name} expected 3 components on axis 0, got {arr.shape!r}")
        if frame is not None:
            raise ValueError(f"{name} has no frame axis; omit --frames")
        comps = arr
    else:
        raise ValueError(f"{name} must be a vector field with ndim 3/4/5, got {arr.ndim}")

    if comps.ndim != 4 or int(comps.shape[0]) != 3:
        raise ValueError(f"{name} must expose 3 components after axis normalization, got {comps.shape!r}")
    if not np.all(np.isfinite(comps)):
        raise ValueError(f"{name} contains non-finite values")
    return comps


def _vector_frame_count(raw: np.ndarray) -> int:
    arr = np.asarray(raw)
    if arr.ndim == 5:
        if arr.shape[-1] == 3 or arr.shape[1] == 3:
            return int(arr.shape[0])
    elif arr.ndim == 4:
        if arr.shape[0] == 3 and arr.shape[-1] != 3:
            return 1
        if arr.shape[-1] == 3:
            if arr.shape[0] == arr.shape[1] == arr.shape[2]:
                return 1
            return int(arr.shape[0])
    elif arr.ndim == 3 and arr.shape[0] == 3:
        return 1
    raise ValueError(f"unsupported vector snapshot rank {arr.ndim}")


def _scalar_frame_count(raw: np.ndarray) -> int:
    arr = np.asarray(raw)
    if arr.ndim == 3:
        return 1
    if arr.ndim == 4:
        return int(arr.shape[0])
    raise ValueError(f"unsupported scalar snapshot rank {arr.ndim}")


def _wavenumbers(n: int, domain_length: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    return (k.reshape(n, 1, 1), k.reshape(1, n, 1), k.reshape(1, 1, n))


def _spectral_derivative(field: np.ndarray, axis: int, kx: np.ndarray, ky: np.ndarray, kz: np.ndarray) -> np.ndarray:
    f_hat = np.fft.fftn(field, axes=(0, 1, 2))
    if axis == 0:
        return np.fft.ifftn(1j * kx * f_hat, axes=(0, 1, 2)).real
    if axis == 1:
        return np.fft.ifftn(1j * ky * f_hat, axes=(0, 1, 2)).real
    if axis == 2:
        return np.fft.ifftn(1j * kz * f_hat, axes=(0, 1, 2)).real
    raise ValueError(f"axis must be 0, 1, or 2; got {axis}")


def _spectral_gradient_from_velocity(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    n = _validate_cubic(u, "u")
    _validate_cubic(v, "v")
    _validate_cubic(w, "w")
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError(f"velocity component shapes must match, got {u.shape!r}, {v.shape!r}, {w.shape!r}")

    kx, ky, kz = _wavenumbers(n, domain_length)
    velocity = (u, v, w)
    grad = np.empty((3, 3) + u.shape, dtype=np.float64)
    for comp in range(3):
        grad[comp, 0] = _spectral_derivative(velocity[comp], 0, kx, ky, kz)
        grad[comp, 1] = _spectral_derivative(velocity[comp], 1, kx, ky, kz)
        grad[comp, 2] = _spectral_derivative(velocity[comp], 2, kx, ky, kz)
    return grad


def _spectral_laplacian(field: np.ndarray, domain_length: float) -> np.ndarray:
    if field.ndim != 3:
        raise ValueError(f"pressure field must be 3D, got {field.shape!r}")
    n = _validate_cubic(field, "pressure")
    kx, ky, kz = _wavenumbers(n, domain_length)
    field_hat = np.fft.fftn(field, axes=(0, 1, 2))
    return np.fft.ifftn(-(kx * kx + ky * ky + kz * kz) * field_hat, axes=(0, 1, 2)).real


def _select_index(omega_field: np.ndarray) -> tuple[int, int, int]:
    omega_mag_sq = (
        omega_field[0] * omega_field[0]
        + omega_field[1] * omega_field[1]
        + omega_field[2] * omega_field[2]
    )
    flat = int(np.argmax(omega_mag_sq))
    return tuple(int(x) for x in np.unravel_index(flat, omega_mag_sq.shape))


def _parse_frames_spec(spec: str, frame_count: int) -> list[int]:
    text = spec.strip()
    if not text or text.lower() == "all":
        return list(range(frame_count))

    frames: list[int] = []
    seen: set[int] = set()
    for token in text.split(","):
        chunk = token.strip()
        if not chunk:
            continue
        if "-" in chunk:
            start_text, end_text = chunk.split("-", 1)
            if not start_text or not end_text:
                raise ValueError(f"invalid frame range {chunk!r}")
            start = int(start_text)
            end = int(end_text)
            if start < 0 or end < 0:
                raise ValueError(f"frame indices must be nonnegative: {chunk!r}")
            if end < start:
                raise ValueError(f"frame range must be increasing: {chunk!r}")
            values = range(start, end + 1)
        else:
            value = int(chunk)
            if value < 0:
                raise ValueError(f"frame indices must be nonnegative: {chunk!r}")
            values = (value,)

        for value in values:
            if value >= frame_count:
                raise ValueError(f"frame {value} is out of range for {frame_count} frame(s)")
            if value not in seen:
                seen.add(value)
                frames.append(value)

    if not frames:
        raise ValueError("no frames selected")
    return frames


def _summary_stats(values: list[float]) -> dict[str, float] | None:
    if not values:
        return None
    arr = np.asarray(values, dtype=np.float64)
    return {
        "min": float(np.min(arr)),
        "mean": float(np.mean(arr)),
        "max": float(np.max(arr)),
    }


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    output = args.output_json
    payload: dict[str, Any] = {
        "schema_version": "1.0.0",
        "contract": CONTRACT,
        "script": SCRIPT_NAME,
        "route_decision": ROUTE_DECISION,
        "input": str(args.input),
        "output": str(output),
        "domain_length": float(args.domain_length),
        "frames_spec": args.frames,
        "status": OK_STATUS,
        "warnings": [],
        "errors": [],
        "changed_paths": [str(output)],
        "authority": _authority_false_flags(),
    }
    payload.update(_control_card())

    try:
        args.domain_length = _finite_float(args.domain_length, "--domain-length")
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [str(exc)]
        return payload, 1
    if args.domain_length <= 0.0:
        payload["status"] = ERROR_STATUS
        payload["errors"] = ["--domain-length must be positive"]
        return payload, 1

    try:
        data = _load_npz(args.input)
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"input_load:{exc}"]
        return payload, 1

    required = ("velocity_snapshots", "omega_snapshots")
    missing = [name for name in required if name not in data]
    if missing:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"missing required field(s): {', '.join(missing)}"]
        return payload, 1

    try:
        velocity_raw = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        omega_raw = np.asarray(data["omega_snapshots"], dtype=np.float64)
        velocity_frame_count = _vector_frame_count(velocity_raw)
        omega_frame_count = _vector_frame_count(omega_raw)
        if velocity_frame_count != omega_frame_count:
            raise ValueError(
                f"velocity and omega frame counts differ: {velocity_frame_count} vs {omega_frame_count}"
            )

        pressure_raw = np.asarray(data["pressure_snapshots"], dtype=np.float64) if "pressure_snapshots" in data else None
        pressure_frame_count = _scalar_frame_count(pressure_raw) if pressure_raw is not None else None
        if pressure_raw is not None and pressure_frame_count != omega_frame_count:
            raise ValueError(
                f"pressure and omega frame counts differ: {pressure_frame_count} vs {omega_frame_count}"
            )
        frame_indices = _parse_frames_spec(args.frames, omega_frame_count)
    except Exception as exc:
        payload["status"] = ERROR_STATUS
        payload["errors"] = [f"input_layout:{exc}"]
        return payload, 1

    payload["frame_count"] = int(omega_frame_count)
    payload["selected_frames"] = [int(frame) for frame in frame_indices]
    payload["selected_frame_count"] = int(len(frame_indices))

    rows: list[dict[str, Any]] = []
    warnings: list[str] = []
    row_errors: list[str] = []
    has_pressure = pressure_raw is not None

    for frame in frame_indices:
        row: dict[str, Any] = {"frame": int(frame), "status": OK_STATUS}
        try:
            velocity = _select_vector_snapshot("velocity_snapshots", velocity_raw, frame)
            omega = _select_vector_snapshot("omega_snapshots", omega_raw, frame)
            if velocity.shape != omega.shape:
                raise ValueError(f"velocity and omega shapes differ: {velocity.shape!r} vs {omega.shape!r}")

            u, v, w = velocity
            omega_x, omega_y, omega_z = omega
            gradient = _spectral_gradient_from_velocity(u, v, w, args.domain_length)
            selected = _select_index(omega)
            i, j, k = selected
            local_grad = np.asarray(gradient[:, :, i, j, k], dtype=np.float64)
            local_S = 0.5 * (local_grad + local_grad.T)
            omega_vec = np.array(
                [float(omega_x[i, j, k]), float(omega_y[i, j, k]), float(omega_z[i, j, k])],
                dtype=np.float64,
            )

            eigenvalues, eigenvectors = np.linalg.eigh(local_S)
            projected = eigenvectors.T @ omega_vec
            omega_norm_sq = float(np.dot(omega_vec, omega_vec))
            lambda1, lambda2, lambda3 = (float(eigenvalues[idx]) for idx in (0, 1, 2))
            omega1, omega2, omega3 = (float(projected[idx]) for idx in (0, 1, 2))
            extensional_gain = 2.0 * lambda3 * (omega3 ** 2)
            middle_damping = -2.0 * abs(lambda2) * (omega2 ** 2)
            compressive_abs_gain = 2.0 * abs(lambda1) * (omega1 ** 2)
            signed_budget = extensional_gain + middle_damping + compressive_abs_gain

            n = int(omega_x.shape[0])
            cell_volume = (args.domain_length / float(n)) ** 3
            omega_mag = np.sqrt(omega_x * omega_x + omega_y * omega_y + omega_z * omega_z)
            omega_l3_domain_norm = float(np.power(np.sum(omega_mag ** 3, dtype=np.float64) * cell_volume, 1.0 / 3.0))

            row.update(
                {
                    "selected_cell": [int(i), int(j), int(k)],
                    "lambda1": lambda1,
                    "lambda2": lambda2,
                    "lambda3": lambda3,
                    "omega_norm_sq": omega_norm_sq,
                    "extensional_gain": extensional_gain,
                    "middle_damping": middle_damping,
                    "compressive_abs_gain": compressive_abs_gain,
                    "signed_budget": signed_budget,
                    "omega_l3_domain_norm": omega_l3_domain_norm,
                    "pressure_laplacian": None,
                }
            )

            if pressure_raw is not None:
                try:
                    pressure_field = _select_scalar_snapshot("pressure_snapshots", pressure_raw, frame)
                    pressure_laplacian = _spectral_laplacian(pressure_field, args.domain_length)
                    row["pressure_laplacian"] = float(pressure_laplacian[i, j, k])
                except Exception as exc:
                    warnings.append(f"frame {frame}:pressure:{exc}")
        except Exception as exc:
            row["status"] = ERROR_STATUS
            row["errors"] = [str(exc)]
            row_errors.append(f"frame {frame}:{exc}")
        rows.append(row)

    valid_rows = [row for row in rows if row.get("status") == OK_STATUS]
    if row_errors:
        payload["status"] = ERROR_STATUS
        payload["errors"] = sorted(set(row_errors))

    payload["rows"] = rows
    payload["warnings"].extend(warnings)
    payload["warnings"] = sorted(set(payload["warnings"]))

    if not valid_rows:
        payload["status"] = ERROR_STATUS
        if not payload["errors"]:
            payload["errors"] = ["no_valid_frames"]
        return payload, 1

    summary_fields = (
        "lambda1",
        "lambda2",
        "lambda3",
        "omega_norm_sq",
        "extensional_gain",
        "middle_damping",
        "compressive_abs_gain",
        "signed_budget",
        "omega_l3_domain_norm",
    )
    aggregate: dict[str, Any] = {
        "frame_count": int(omega_frame_count),
        "selected_frame_count": int(len(frame_indices)),
        "valid_frame_count": int(len(valid_rows)),
        "selected_frames": [int(frame) for frame in frame_indices],
    }
    for field in summary_fields:
        values = [float(row[field]) for row in valid_rows if field in row and row[field] is not None]
        stats = _summary_stats(values)
        if stats is not None:
            aggregate[field] = stats
    pressure_values = [
        float(row["pressure_laplacian"])
        for row in valid_rows
        if row.get("pressure_laplacian") is not None
    ]
    pressure_stats = _summary_stats(pressure_values)
    if pressure_stats is not None:
        aggregate["pressure_laplacian"] = pressure_stats
    aggregate["has_pressure_snapshots"] = bool(has_pressure)
    payload["aggregate"] = aggregate

    return payload, 0 if payload["status"] == OK_STATUS else 1


def _emit(payload: dict[str, Any], args: argparse.Namespace) -> None:
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        payload["changed_paths"] = [str(args.output_json)]
        args.output_json.write_text(
            json.dumps(
                payload,
                indent=2 if args.pretty else None,
                sort_keys=True,
                ensure_ascii=False,
                allow_nan=False,
            ),
            encoding="utf-8",
        )
    print(
        json.dumps(
            payload,
            indent=2 if args.pretty else None,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
    )


def main() -> int:
    args = _parse_args()
    payload, returncode = _build_payload(args)
    _emit(payload, args)
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())
