#!/usr/bin/env python3
"""Interior pointwise vorticity budget diagnostic for NS snapshots."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_interior_vorticity_budget_diagnostic.py"
CONTRACT = "ns_interior_vorticity_budget_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_NS_INTERIOR_VORTICITY_BUDGET_DIAGNOSTIC"
DEFAULT_OUTPUT = Path("outputs/ns_interior_vorticity_budget_diagnostic.json")
DEFAULT_DOMAIN_LENGTH = 2.0 * math.pi
OK_STATUS = "ok"
ERROR_STATUS = "error"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Raw NPZ with velocity_snapshots and omega_snapshots")
    parser.add_argument(
        "--frame",
        type=int,
        help="Frame index to extract from 4D fields",
        default=None,
    )
    parser.add_argument("--index", type=int, nargs=3, metavar=("I", "J", "K"), default=None, help="Cell index i j k")
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="JSON output path (required fields only)",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=DEFAULT_DOMAIN_LENGTH,
        help="Domain side length for spectral derivatives",
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
        "O": "Pointwise interior NS diagnostic for one selected cell at fixed frame.",
        "R": "Compute spectral velocity gradients, strain eigensystem, budget terms, and local pressure Laplacian terms.",
        "C": "Deterministic numerical diagnostic from raw NPZ snapshots.",
        "S": "Fail-closed on malformed archives, out-of-range indices, non-finite values, or non-cubic grids.",
        "L": "status=ok only when all required fields are finite and computed terms are well-defined.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or promotion authority is claimed.",
        "F": "This is empirical finite-domain evidence only; authority flags remain false.",
    }


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {name: np.asarray(data[name]) for name in data.files}


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return float(parsed)


def _nonnegative(value: int, name: str) -> int:
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


def _ensure_nonnegative_optional(value: int | None, name: str) -> int | None:
    if value is None:
        return None
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


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
            if arr.shape[0] == arr.shape[1] == arr.shape[2]:
                pass
            elif int(arr.shape[0]) == 1:
                arr = arr[0]
            else:
                raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frame")
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
                    raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frame")
                arr = arr[0]
            else:
                if frame < 0 or frame >= int(arr.shape[0]):
                    raise ValueError(
                        f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)"
                    )
                arr = arr[frame]
            comps = np.moveaxis(arr, -1, 0)
        elif arr.shape[1] == 3:
            if frame is None:
                if int(arr.shape[0]) != 1:
                    raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frame")
                comps = arr[0]
            else:
                if frame < 0 or frame >= int(arr.shape[0]):
                    raise ValueError(
                        f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)"
                    )
                comps = arr[frame]
        else:
            raise ValueError(f"{name} expected 3-vector channels on axis 1 or -1, got {arr.shape!r}")
    elif arr.ndim == 3:
        if arr.shape[0] != 3:
            raise ValueError(f"{name} expected 3 components on axis 0, got {arr.shape!r}")
        if frame is not None:
            raise ValueError(f"{name} has no frame axis; omit --frame")
        comps = arr
    elif arr.ndim == 4:
        if arr.shape[-1] == 3:
            if frame is None:
                if arr.shape[0] == arr.shape[1] == arr.shape[2]:
                    arr = arr
                elif int(arr.shape[0]) == 1:
                    arr = arr[0]
                else:
                    raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frame")
            else:
                if frame < 0 or frame >= int(arr.shape[0]):
                    raise ValueError(
                        f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)"
                    )
                arr = arr[frame]
            comps = np.moveaxis(arr, -1, 0)
        elif arr.shape[0] == 3 and arr.shape[-1] != 3:
            if frame is not None:
                raise ValueError(f"{name} has no frame axis; omit --frame")
            comps = arr
        else:
            raise ValueError(f"{name} expected 3-vector channels on axis 0 or -1, got {arr.shape!r}")
    else:
        raise ValueError(f"{name} must be vector field with ndim 3/4, got {arr.ndim}")

    if comps.ndim != 4 or int(comps.shape[0]) != 3:
        raise ValueError(f"{name} must expose 3 components after axis normalization, got {comps.shape!r}")
    if not np.all(np.isfinite(comps)):
        raise ValueError(f"{name} contains non-finite values")
    return comps


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


def _select_index(omega_field: np.ndarray, override: list[int] | None) -> tuple[int, int, int]:
    if override is not None:
        if len(override) != 3:
            raise ValueError("index must contain exactly 3 entries")
        i, j, k = (int(v) for v in override)
        _nonnegative(i, "index[0]")
        _nonnegative(j, "index[1]")
        _nonnegative(k, "index[2]")
        n = omega_field.shape[1]
        if i >= n or j >= n or k >= n:
            raise ValueError(f"index out of range for grid size {n}")
        return i, j, k

    # omega_field is (3,N,N,N), so this is |omega|^2.
    omega_mag_sq = (
        omega_field[0] * omega_field[0]
        + omega_field[1] * omega_field[1]
        + omega_field[2] * omega_field[2]
    )
    flat = int(np.argmax(omega_mag_sq))
    return tuple(int(x) for x in np.unravel_index(flat, omega_mag_sq.shape))


def _make_output(
    args: argparse.Namespace,
    payload: dict[str, Any],
    status: str,
    changed_paths: list[str],
    budget: dict[str, float] | None = None,
    pressure: dict[str, float | None] | None = None,
    norms: dict[str, float] | None = None,
) -> dict[str, Any]:
    base = {
        "schema_version": "1.0.0",
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "script": SCRIPT_NAME,
        "input": str(args.input),
        "output": str(args.output_json),
        "domain_length": float(args.domain_length),
        "status": status,
        "frame": None if args.frame is None else int(args.frame),
        "authority": _authority_false_flags(),
        "changed_paths": changed_paths,
        "warnings": [],
        "errors": [],
    }
    base.update(_control_card())
    if budget is not None:
        base["budget"] = budget
    if pressure is not None:
        base["pressure"] = pressure
    if norms is not None:
        base["norms"] = norms
    base.update(payload)
    return base


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
    else:
        payload["changed_paths"] = []
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
    if args.frame is not None:
        try:
            args.frame = _ensure_nonnegative_optional(args.frame, "--frame")
        except ValueError as exc:
            payload = _make_output(args, {"errors": [str(exc)]}, ERROR_STATUS, [])
            _emit(payload, args)
            return 1
    args.domain_length = _finite_float(args.domain_length, "--domain-length")
    if args.domain_length <= 0.0:
        payload = _make_output(args, {"errors": ["--domain-length must be positive"]}, ERROR_STATUS, [])
        _emit(payload, args)
        return 1

    base_payload: dict[str, Any] = {}
    changed_paths: list[str] = []
    status = OK_STATUS
    errors: list[str] = []

    try:
        data = _load_npz(args.input)
    except Exception as exc:
        errors.append(f"input_load:{exc}")
        status = ERROR_STATUS
        _emit(_make_output(args, {"errors": errors}, status, changed_paths), args)
        return 1

    if "velocity_snapshots" not in data or "omega_snapshots" not in data:
        errors.append("missing required field: velocity_snapshots and/or omega_snapshots")
        status = ERROR_STATUS

    if status == ERROR_STATUS:
        _emit(_make_output(args, {"errors": errors}, status, changed_paths), args)
        return 1

    try:
        velocity = _select_vector_snapshot("velocity_snapshots", data["velocity_snapshots"], args.frame)
        omega = _select_vector_snapshot("omega_snapshots", data["omega_snapshots"], args.frame)
        if velocity.shape != omega.shape:
            raise ValueError(f"velocity and omega shapes differ: {velocity.shape!r} vs {omega.shape!r}")

        u, v, w = velocity
        omega_x, omega_y, omega_z = omega
        gradient = _spectral_gradient_from_velocity(u, v, w, args.domain_length)
    except Exception as exc:
        errors.append(f"load_or_gradient:{exc}")
        status = ERROR_STATUS
        _emit(_make_output(args, {"errors": errors}, status, changed_paths), args)
        return 1

    try:
        selected = _select_index(omega, args.index)
    except Exception as exc:
        errors.append(f"cell_selection:{exc}")
        status = ERROR_STATUS
        _emit(_make_output(args, {"errors": errors}, status, changed_paths), args)
        return 1

    i, j, k = selected
    local_grad = np.asarray(gradient[:, :, i, j, k], dtype=np.float64)
    local_S = 0.5 * (local_grad + local_grad.T)
    lambda1, lambda2, lambda3 = 0.0, 0.0, 0.0
    omega1, omega2, omega3 = 0.0, 0.0, 0.0
    omega_vec = np.array([float(omega_x[i, j, k]), float(omega_y[i, j, k]), float(omega_z[i, j, k])], dtype=np.float64)

    try:
        eigenvalues, eigenvectors = np.linalg.eigh(local_S)
        projected = eigenvectors.T @ omega_vec
        omega1, omega2, omega3 = (float(projected[idx]) for idx in (0, 1, 2))
        lambda1, lambda2, lambda3 = (float(eigenvalues[idx]) for idx in (0, 1, 2))
        omega_norm_sq = float(np.dot(omega_vec, omega_vec))
    except Exception as exc:
        errors.append(f"spectral_decomp:{exc}")
        status = ERROR_STATUS
        _emit(_make_output(args, {"errors": errors}, status, changed_paths), args)
        return 1

    extensional_gain = 2.0 * lambda3 * (omega3 ** 2)
    middle_damping = -2.0 * abs(lambda2) * (omega2 ** 2)
    compressive_abs_gain = 2.0 * abs(lambda1) * (omega1 ** 2)
    signed_budget = extensional_gain + middle_damping + compressive_abs_gain

    n = omega_x.shape[0]
    cell_volume = (args.domain_length / float(n)) ** 3
    omega_mag = np.sqrt(omega_x * omega_x + omega_y * omega_y + omega_z * omega_z)
    omega_l3_norm = float(np.power(np.sum(omega_mag ** 3) * cell_volume, 1.0 / 3.0))

    budget = {
        "lambda1": lambda1,
        "lambda2": lambda2,
        "lambda3": lambda3,
        "omega1": omega1,
        "omega2": omega2,
        "omega3": omega3,
        "omega_norm_sq": omega_norm_sq,
        "extensional_gain": extensional_gain,
        "middle_damping": middle_damping,
        "compressive_abs_gain": compressive_abs_gain,
        "signed_budget": signed_budget,
    }

    pressure_payload: dict[str, float | None] = {
        "pressure_value": None,
        "pressure_laplacian": None,
        "negative_pressure_laplacian": None,
    }
    if "pressure_snapshots" in data:
        try:
            pressure_field = _select_scalar_snapshot("pressure_snapshots", data["pressure_snapshots"], args.frame)
            pressure_laplacian = _spectral_laplacian(pressure_field, args.domain_length)
            pressure_payload = {
                "pressure_value": float(pressure_field[i, j, k]),
                "pressure_laplacian": float(pressure_laplacian[i, j, k]),
                "negative_pressure_laplacian": float(-pressure_laplacian[i, j, k]),
            }
        except Exception as exc:
            errors.append(f"pressure:{exc}")

    norms = {
        "omega_l3_norm": omega_l3_norm,
        "volume_element": cell_volume,
        "grid_size": int(n),
    }

    base_payload = {
        "selected_cell": [i, j, k],
        "selection": "provided_index" if args.index is not None else "worst_omega_cell",
        "budget": budget,
        "pressure": pressure_payload,
        "norms": norms,
        "errors": errors,
    }

    payload = _make_output(args, base_payload, status, changed_paths)
    if errors:
        if status != ERROR_STATUS:
            payload["warnings"] = sorted(set(errors))
        else:
            payload["errors"] = sorted(set(errors))
    returncode = 0 if status == OK_STATUS else 1
    _emit(payload, args)
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())
