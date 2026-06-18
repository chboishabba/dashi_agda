#!/usr/bin/env python3
"""Fail-closed producer for derived NS boundary tensor archives.

This script reads periodic velocity/pressure data from a single ``.npz`` file,
derives the tensors consumed by ``scripts/ns_boundary_preflight_diagnostic.py``,
and writes a deterministic derived ``.npz`` archive.

Required output arrays:

* ``lambda2``
* ``g12``
* ``B_k``
* ``pressure_hessian_norm``
* ``beta``
* ``time`` is optional

Optional output arrays:

* ``velocity_hessian_norm_squared`` when ``--include-velocity-hessian`` is set
* ``strain_hessian_norm_squared`` when ``--include-velocity-hessian`` is set
* ``antisym_hessian_norm_squared`` when ``--include-velocity-hessian`` is set

The producer accepts either real-space velocity keys ``u``, ``v``, ``w`` or
spectral velocity keys ``u_hat``, ``v_hat``, ``w_hat``.  Pressure is optional:
if it is absent, the script tries to recover the pressure via the periodic
incompressible pressure Poisson equation and then computes the Hessian norm.
If that is not feasible, the run fails closed unless ``--allow-zero-pressure``
is set, in which case the archive stores a zero pressure-Hessian norm field.
"""

from __future__ import annotations

import argparse
import io
import json
import math
import os
import tempfile
import zipfile
from pathlib import Path
from typing import Any

import numpy as np


DOMAIN_DEFAULT = 2.0 * np.pi
# The real DNS archive is float32 and FFT roundoff leaves tiny imaginary
# residues after inverse transforms.  This tolerance is relative to the real
# scale and remains fail-closed for material complex leakage.
REAL_TOL = 1.0e-6
DIV_TOL = 1.0e-8
DEFAULT_BETA_VALUE = 0.0
INPUT_VELOCITY_KEYS = (("u", "v", "w"), ("u_hat", "v_hat", "w_hat"))
INPUT_PRESSURE_KEYS = (("pressure",), ("p",), ("pressure_hat",), ("p_hat",))
VALID_AXIS_ORDERS = {"x,y,z", "z,y,x"}
PRODUCER_NAME = "scripts/ns_boundary_derived_tensor_archive.py"


def _scalar_metadata(data: Any, *names: str) -> tuple[Any | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape != ():
            raise ValueError(f"{name} metadata must be scalar, got shape {value.shape!r}")
        scalar = value.item()
        if isinstance(scalar, bytes):
            scalar = scalar.decode("utf-8")
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        return scalar, name
    return None, None


def _optional_text(data: Any, *names: str) -> tuple[str | None, str | None]:
    value, name = _scalar_metadata(data, *names)
    if value is None:
        return None, None
    return str(value), name


def _as_finite_real(name: str, value: Any) -> float:
    scalar = float(value)
    if not np.isfinite(scalar):
        raise ValueError(f"{name} must be finite, got {value!r}")
    return scalar


def _validate_output_path(path: Path) -> Path:
    if path.suffix.lower() != ".npz":
        raise ValueError("output path must have a .npz suffix")
    return path


def _prepare_output_path(path: Path) -> Path:
    path = _validate_output_path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        out = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in out:
        try:
            meta = json.loads(str(np.asarray(out["meta_json"]).item()))
        except Exception as exc:
            raise ValueError(f"meta_json could not be parsed as JSON: {exc}") from exc
        for key in ("N", "domain_length", "grid_spacing", "axis_order"):
            if key in meta and key not in out:
                out[key] = np.asarray(meta[key])
    return out


def _realize_array(name: str, value: Any, *, tol: float = REAL_TOL) -> np.ndarray:
    array = np.asarray(value)
    if np.iscomplexobj(array):
        imag_max = float(np.max(np.abs(array.imag))) if array.size else 0.0
        real_scale = float(np.max(np.abs(array.real))) if array.size else 0.0
        scale = max(1.0, real_scale)
        if imag_max > tol * scale:
            raise ValueError(
                f"{name} has non-negligible imaginary residue after inverse FFT: "
                f"max_imag={imag_max:.3e}, scale={scale:.3e}"
            )
        array = array.real
    array = np.asarray(array, dtype=np.float64)
    if array.ndim not in {3, 4}:
        raise ValueError(f"{name} must be 3D or 4D with optional leading time axis, got {array.shape!r}")
    if len(set(array.shape[-3:])) != 1:
        raise ValueError(f"{name} must be cubic in its spatial dimensions, got {array.shape!r}")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def _standardize_axis_order(array: np.ndarray, axis_order: str) -> np.ndarray:
    if axis_order not in VALID_AXIS_ORDERS:
        raise ValueError(f"axis_order must be one of {sorted(VALID_AXIS_ORDERS)!r}, got {axis_order!r}")
    if axis_order == "x,y,z":
        return np.asarray(array)
    if array.ndim == 3:
        return np.transpose(array, (2, 1, 0))
    if array.ndim == 4:
        return np.transpose(array, (0, 3, 2, 1))
    raise ValueError(f"unsupported array rank for axis reordering: {array.shape!r}")


def _spatial_axes(ndim: int) -> tuple[int, int, int]:
    if ndim == 3:
        return (0, 1, 2)
    if ndim == 4:
        return (1, 2, 3)
    raise ValueError(f"expected a 3D or 4D field, got ndim={ndim}")


def _spatial_axis_index(ndim: int, axis: int) -> int:
    if axis not in {0, 1, 2}:
        raise ValueError(f"axis must be 0, 1, or 2, got {axis}")
    return axis if ndim == 3 else axis + 1


def _ordered_cubic_shape(array: np.ndarray) -> tuple[int, ...]:
    spatial = array.shape[-3:]
    if len(set(spatial)) != 1:
        raise ValueError(f"spatial grid must be cubic, got shape {array.shape!r}")
    return array.shape


def _load_velocity_bundle(data: dict[str, np.ndarray]) -> tuple[np.ndarray, tuple[str, str, str], str]:
    real_keys = INPUT_VELOCITY_KEYS[0]
    spectral_keys = INPUT_VELOCITY_KEYS[1]
    real_present = all(key in data for key in real_keys)
    spectral_present = all(key in data for key in spectral_keys)
    if real_present:
        arrays = tuple(_realize_array(key, data[key]) for key in real_keys)
        return arrays[0], real_keys, "real"
    if spectral_present:
        arrays = []
        for key in spectral_keys:
            spectral = np.asarray(data[key], dtype=np.complex128)
            physical = np.fft.ifftn(spectral, axes=_spatial_axes(spectral.ndim))
            arrays.append(_realize_array(f"{key} (ifft)", physical))
        return arrays[0], spectral_keys, "spectral"
    missing_real = [key for key in real_keys if key not in data]
    missing_spectral = [key for key in spectral_keys if key not in data]
    raise ValueError(
        "input NPZ must provide either u/v/w or u_hat/v_hat/w_hat; "
        f"missing real-space keys={missing_real}, missing spectral keys={missing_spectral}"
    )


def _snapshot_axis_to_front(array: np.ndarray, snapshot_index: int | None, label: str) -> np.ndarray:
    field = np.asarray(array)
    if snapshot_index is None:
        return field
    if field.ndim < 4:
        raise ValueError(f"--snapshot-index requires {label} to have a leading snapshot axis")
    if snapshot_index < 0 or snapshot_index >= int(field.shape[0]):
        raise ValueError(
            f"--snapshot-index {snapshot_index} is out of range for {label} with {field.shape[0]} snapshots"
        )
    return np.asarray(field[snapshot_index])


def _load_velocity_components(
    data: dict[str, np.ndarray],
    snapshot_index: int | None,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, tuple[str, str, str] | tuple[str], str]:
    if "velocity_snapshots" in data:
        snapshots = _snapshot_axis_to_front(data["velocity_snapshots"], snapshot_index, "velocity_snapshots")
        velocity = np.asarray(snapshots)
        if velocity.ndim not in {4, 5} or velocity.shape[-1] != 3:
            raise ValueError(
                "velocity_snapshots must have shape (..., N, N, N, 3), "
                f"got {velocity.shape!r}"
            )
        components = tuple(_realize_array(f"velocity_snapshots[...,{idx}]", velocity[..., idx]) for idx in range(3))
        return components[0], components[1], components[2], ("velocity_snapshots",), "snapshot-real"

    real_keys = INPUT_VELOCITY_KEYS[0]
    spectral_keys = INPUT_VELOCITY_KEYS[1]
    real_present = all(key in data for key in real_keys)
    spectral_present = all(key in data for key in spectral_keys)
    if real_present:
        components = tuple(_realize_array(key, data[key]) for key in real_keys)
        source_keys = real_keys
        source_kind = "real"
    elif spectral_present:
        components = []
        for key in spectral_keys:
            spectral = np.asarray(data[key], dtype=np.complex128)
            physical = np.fft.ifftn(spectral, axes=_spatial_axes(spectral.ndim))
            components.append(_realize_array(f"{key} (ifft)", physical))
        components = tuple(components)  # type: ignore[assignment]
        source_keys = spectral_keys
        source_kind = "spectral"
    else:
        missing_real = [key for key in real_keys if key not in data]
        missing_spectral = [key for key in spectral_keys if key not in data]
        raise ValueError(
            "input NPZ must provide either u/v/w or u_hat/v_hat/w_hat; "
            f"missing real-space keys={missing_real}, missing spectral keys={missing_spectral}"
        )

    u, v, w = components
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError(f"velocity component shapes must match, got {u.shape!r}, {v.shape!r}, {w.shape!r}")
    return u, v, w, source_keys, source_kind


def _load_optional_pressure(
    data: dict[str, np.ndarray],
    snapshot_index: int | None,
) -> tuple[np.ndarray | None, str | None, str | None]:
    if "pressure_snapshots" in data:
        pressure = _snapshot_axis_to_front(data["pressure_snapshots"], snapshot_index, "pressure_snapshots")
        return _realize_array("pressure_snapshots", pressure), "pressure_snapshots", "real"

    for keyset, kind in ((("pressure",), "real"), (("p",), "real"), (("pressure_hat",), "spectral"), (("p_hat",), "spectral")):
        key = keyset[0]
        if key not in data:
            continue
        if kind == "real":
            pressure = _realize_array(key, data[key])
        else:
            spectral = np.asarray(data[key], dtype=np.complex128)
            pressure = _realize_array(f"{key} (ifft)", np.fft.ifftn(spectral, axes=_spatial_axes(spectral.ndim)))
        return pressure, key, kind
    return None, None, None


def _validate_domain_length(data: dict[str, np.ndarray], n: int, override: float | None) -> tuple[float, str]:
    if override is not None:
        domain_length = _as_finite_real("--domain-length", override)
        if domain_length <= 0.0:
            raise ValueError("--domain-length must be positive")
        for name in ("domain_length", "length"):
            if name not in data:
                continue
            declared = _as_finite_real(name, _scalar_metadata(data, name)[0])
            if not np.isclose(declared, domain_length, rtol=1.0e-12, atol=1.0e-12):
                raise ValueError(
                    f"{name} metadata {declared:.17g} does not match --domain-length {domain_length:.17g}"
                )
        spacing_value, spacing_name = _scalar_metadata(data, "grid_spacing")
        if spacing_value is not None:
            grid_spacing = _as_finite_real(str(spacing_name), spacing_value)
            expected = domain_length / float(n)
            if not np.isclose(grid_spacing, expected, rtol=1.0e-12, atol=1.0e-12):
                raise ValueError(
                    f"{spacing_name} metadata {grid_spacing:.17g} does not match domain_length/N "
                    f"{expected:.17g}"
                )
        return domain_length, "cli"

    domain_value, domain_name = _scalar_metadata(data, "domain_length", "length")
    spacing_value, spacing_name = _scalar_metadata(data, "grid_spacing")
    if domain_value is None:
        if spacing_value is None:
            raise ValueError(
                "domain_length metadata is required; supply domain_length/length, grid_spacing, or --domain-length"
            )
        grid_spacing = _as_finite_real(str(spacing_name), spacing_value)
        if grid_spacing <= 0.0:
            raise ValueError(f"{spacing_name} must be positive")
        return grid_spacing * float(n), f"derived:{spacing_name}"

    domain_length = _as_finite_real(str(domain_name), domain_value)
    if domain_length <= 0.0:
        raise ValueError(f"{domain_name} must be positive")

    if spacing_value is not None:
        grid_spacing = _as_finite_real(str(spacing_name), spacing_value)
        if grid_spacing <= 0.0:
            raise ValueError(f"{spacing_name} must be positive")
        expected = domain_length / float(n)
        if not np.isclose(grid_spacing, expected, rtol=1.0e-12, atol=1.0e-12):
            raise ValueError(
                f"grid_spacing metadata {grid_spacing:.17g} does not match domain_length/N "
                f"{expected:.17g}"
            )

    return domain_length, str(domain_name)


def _validate_n(data: dict[str, np.ndarray], shape: tuple[int, ...]) -> int:
    spatial = shape[-3:]
    if len(set(spatial)) != 1:
        raise ValueError(f"input field must have cubic spatial dimensions, got {shape!r}")
    n = int(spatial[0])
    declared_n, name = _scalar_metadata(data, "N")
    if declared_n is not None:
        if int(declared_n) != declared_n:
            raise ValueError(f"{name} must be an integer, got {declared_n!r}")
        if int(declared_n) != n:
            raise ValueError(f"{name}={int(declared_n)} does not match the spatial grid size {n}")
    return n


def _time_array(data: dict[str, np.ndarray], n_snapshots: int) -> tuple[np.ndarray | None, str | None]:
    if "time" in data:
        time = np.asarray(data["time"])
        if time.shape == ():
            if n_snapshots != 1:
                raise ValueError("time must be 1D when multiple snapshots are present")
            return np.asarray(time), "time"
        if time.ndim != 1:
            raise ValueError(f"time must be scalar or 1D, got shape {time.shape!r}")
        if len(time) != n_snapshots:
            raise ValueError(f"time length {len(time)} does not match the number of snapshots {n_snapshots}")
        return np.asarray(time, dtype=np.float64), "time"
    if "t" in data:
        time = np.asarray(data["t"])
        if time.shape == ():
            if n_snapshots != 1:
                raise ValueError("t must be 1D when multiple snapshots are present")
            return np.asarray(time), "t"
        if time.ndim != 1:
            raise ValueError(f"t must be scalar or 1D, got shape {time.shape!r}")
        if len(time) != n_snapshots:
            raise ValueError(f"t length {len(time)} does not match the number of snapshots {n_snapshots}")
        return np.asarray(time, dtype=np.float64), "t"
    return None, None


def _time_for_snapshot(time: np.ndarray | None, snapshot_index: int | None) -> np.ndarray | None:
    if time is None or snapshot_index is None:
        return time
    time_array = np.asarray(time)
    if time_array.shape == ():
        return time_array
    if time_array.ndim != 1:
        raise ValueError(f"time must be scalar or 1D, got shape {time_array.shape!r}")
    if snapshot_index >= len(time_array):
        raise ValueError(f"--snapshot-index {snapshot_index} is out of range for time length {len(time_array)}")
    return np.asarray(time_array[snapshot_index])


def _resolve_series_shape(field: np.ndarray) -> tuple[int, ...]:
    shape = _ordered_cubic_shape(field)
    if field.ndim == 3:
        return shape
    if field.ndim == 4 and shape[0] <= 0:
        raise ValueError("time axis must be non-empty")
    return shape


def _frequency_grid(n: int, length: float, ndim: int, axis: int) -> np.ndarray:
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=length / float(n))
    shape = [1] * ndim
    shape[_spatial_axis_index(ndim, axis)] = n
    return k.reshape(shape)


def _spectral_derivative(field: np.ndarray, axis: int, length: float) -> np.ndarray:
    scalar = np.asarray(field, dtype=np.float64)
    if scalar.ndim not in {3, 4}:
        raise ValueError(f"field must be 3D or 4D, got shape {scalar.shape!r}")
    axes = _spatial_axes(scalar.ndim)
    n = int(scalar.shape[axes[0]])
    if any(int(scalar.shape[a]) != n for a in axes):
        raise ValueError(f"field must be cubic in space, got shape {scalar.shape!r}")
    multiplier = 1j * _frequency_grid(n, length, scalar.ndim, axis)
    transformed = np.fft.fftn(scalar, axes=axes)
    derivative = np.fft.ifftn(multiplier * transformed, axes=axes)
    return _realize_array("spectral derivative", derivative)


def _spectral_hessian(field: np.ndarray, length: float) -> np.ndarray:
    scalar = np.asarray(field, dtype=np.float64)
    if scalar.ndim not in {3, 4}:
        raise ValueError(f"field must be 3D or 4D, got shape {scalar.shape!r}")
    axes = _spatial_axes(scalar.ndim)
    n = int(scalar.shape[axes[0]])
    if any(int(scalar.shape[a]) != n for a in axes):
        raise ValueError(f"field must be cubic in space, got shape {scalar.shape!r}")
    field_hat = np.fft.fftn(scalar, axes=axes)
    hessian = np.empty((3, 3) + scalar.shape, dtype=np.float64)
    k = [_frequency_grid(n, length, scalar.ndim, axis) for axis in range(3)]
    for i in range(3):
        for j in range(3):
            hessian[i, j] = np.fft.ifftn(-(k[i] * k[j]) * field_hat, axes=axes).real
    return hessian


def _velocity_gradient(u: np.ndarray, v: np.ndarray, w: np.ndarray, length: float) -> np.ndarray:
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError(f"velocity component shapes differ: {u.shape!r}, {v.shape!r}, {w.shape!r}")
    grad = np.empty((3, 3) + u.shape, dtype=np.float64)
    for component_index, component in enumerate((u, v, w)):
        for axis in range(3):
            grad[component_index, axis] = _spectral_derivative(component, axis, length)
    return grad


def _strain_tensor(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    if tensor.ndim < 5 or tensor.shape[:2] != (3, 3):
        raise ValueError(f"grad must have shape (3,3,...) , got {tensor.shape!r}")
    return 0.5 * (tensor + np.swapaxes(tensor, 0, 1))


def _antisym_tensor(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    if tensor.ndim < 5 or tensor.shape[:2] != (3, 3):
        raise ValueError(f"grad must have shape (3,3,...) , got {tensor.shape!r}")
    return 0.5 * (tensor - np.swapaxes(tensor, 0, 1))


def _vorticity_from_gradient(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    omega = np.empty((3,) + tensor.shape[2:], dtype=np.float64)
    omega[0] = tensor[2, 1] - tensor[1, 2]
    omega[1] = tensor[0, 2] - tensor[2, 0]
    omega[2] = tensor[1, 0] - tensor[0, 1]
    return omega


def _tensor_frobenius_squared(tensor: np.ndarray) -> np.ndarray:
    field = np.asarray(tensor, dtype=np.float64)
    return np.sum(field * field, axis=(0, 1))


def _solve_periodic_poisson_negative_laplacian(rhs: np.ndarray, length: float) -> np.ndarray:
    source = np.asarray(rhs, dtype=np.float64)
    if source.ndim not in {3, 4}:
        raise ValueError(f"rhs must be 3D or 4D, got shape {source.shape!r}")
    axes = _spatial_axes(source.ndim)
    n = int(source.shape[axes[0]])
    if any(int(source.shape[a]) != n for a in axes):
        raise ValueError(f"rhs must be cubic in space, got shape {source.shape!r}")
    k = [_frequency_grid(n, length, source.ndim, axis) for axis in range(3)]
    k_squared = k[0] * k[0] + k[1] * k[1] + k[2] * k[2]
    rhs_hat = np.fft.fftn(source, axes=axes)
    pressure_hat = np.zeros_like(rhs_hat, dtype=np.complex128)
    mask = k_squared > 0.0
    pressure_hat[mask] = rhs_hat[mask] / k_squared[mask]
    pressure = np.fft.ifftn(pressure_hat, axes=axes)
    return _realize_array("poisson pressure", pressure)


def _strain_eigensystem(strain: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    matrices = np.moveaxis(strain, (0, 1), (-2, -1))
    eigenvalues, eigenvectors = np.linalg.eigh(matrices)
    return eigenvalues, eigenvectors


def _matrix_gradient_tensor(tensor: np.ndarray, length: float, label: str) -> np.ndarray:
    tensor = np.asarray(tensor, dtype=np.float64)
    if tensor.ndim not in {5, 6} or tensor.shape[:2] != (3, 3):
        raise ValueError(f"{label} must have shape (3,3,...) , got {tensor.shape!r}")
    grad = np.empty((3, 3, 3) + tensor.shape[2:], dtype=np.float64)
    for i in range(3):
        for j in range(3):
            for axis in range(3):
                grad[i, j, axis] = _spectral_derivative(tensor[i, j], axis, length)
    return grad


def _strain_gradient_tensor(strain: np.ndarray, length: float) -> np.ndarray:
    return _matrix_gradient_tensor(strain, length, "strain")


def _matrix_gradient_norm_squared(matrix_gradient: np.ndarray, label: str) -> np.ndarray:
    tensor = np.asarray(matrix_gradient, dtype=np.float64)
    if tensor.ndim not in {6, 7} or tensor.shape[:3] != (3, 3, 3):
        raise ValueError(f"{label} must have shape (3,3,3,...) , got {tensor.shape!r}")
    total = np.sum(tensor * tensor, axis=(0, 1, 2))
    if not np.all(np.isfinite(total)):
        raise ValueError(f"{label} contains non-finite values")
    if np.any(total < -1.0e-9):
        raise ValueError(f"{label} contains negative values")
    return np.maximum(total, 0.0)


def _compute_B_k(eigenvectors: np.ndarray, strain_gradient: np.ndarray) -> np.ndarray:
    e1 = np.asarray(eigenvectors[..., :, 0], dtype=np.float64)
    e2 = np.asarray(eigenvectors[..., :, 1], dtype=np.float64)
    components: list[np.ndarray] = []
    for axis in range(3):
        local_gradient = strain_gradient[:, :, axis]
        projection = np.einsum("...i,ij...,...j->...", e1, local_gradient, e2)
        components.append(2.0 * np.abs(projection) ** 2)
    stacked = np.stack(components, axis=0)
    return np.max(stacked, axis=0)


def _pressure_hessian_norm_from_pressure(pressure: np.ndarray, length: float) -> np.ndarray:
    hessian = _spectral_hessian(pressure, length)
    return np.sqrt(np.sum(hessian * hessian, axis=(0, 1)))


def _velocity_hessian_norm_squared(u: np.ndarray, v: np.ndarray, w: np.ndarray, length: float) -> np.ndarray:
    total, _, _ = _velocity_hessian_split_norm_squared(u, v, w, length)
    return total


def _velocity_hessian_split_norm_squared(
    u: np.ndarray, v: np.ndarray, w: np.ndarray, length: float
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    grad = _velocity_gradient(u, v, w, length)
    strain_gradient = _matrix_gradient_tensor(_strain_tensor(grad), length, "strain")
    antisym_gradient = _matrix_gradient_tensor(_antisym_tensor(grad), length, "antisymmetric velocity gradient")
    strain_total = _matrix_gradient_norm_squared(strain_gradient, "strain_hessian_norm_squared")
    antisym_total = _matrix_gradient_norm_squared(antisym_gradient, "antisym_hessian_norm_squared")
    total = strain_total + antisym_total
    if not np.all(np.isfinite(total)):
        raise ValueError("velocity_hessian_norm_squared contains non-finite values")
    if np.any(total < -1.0e-9):
        raise ValueError("velocity_hessian_norm_squared contains negative values")
    return np.maximum(total, 0.0), np.maximum(strain_total, 0.0), np.maximum(antisym_total, 0.0)


def _beta_value(args: argparse.Namespace) -> float:
    if args.beta_value is None:
        return DEFAULT_BETA_VALUE
    value = _as_finite_real("--beta-value", args.beta_value)
    return value


def _jsonable_shape(shape: tuple[int, ...] | list[int]) -> list[int]:
    return [int(value) for value in shape]


def _build_manifest(
    *,
    input_path: Path,
    output_path: Path,
    input_keys: list[str],
    velocity_source: str,
    velocity_keys: tuple[str, str, str],
    pressure_key: str | None,
    pressure_mode: str,
    time_key: str | None,
    axis_order: str,
    domain_length: float,
    domain_length_source: str,
    grid_spacing: float,
    n: int,
    series_shape: tuple[int, ...],
    output_time_shape: tuple[int, ...] | None,
    beta_value: float,
    include_velocity_hessian: bool,
) -> dict[str, Any]:
    output_keys = ["lambda2", "g12", "B_k", "pressure_hessian_norm", "beta"]
    if include_velocity_hessian:
        output_keys.append("velocity_hessian_norm_squared")
        output_keys.append("strain_hessian_norm_squared")
        output_keys.append("antisym_hessian_norm_squared")
    if output_time_shape is not None:
        output_keys.append("time")
    shapes = {
        "lambda2": _jsonable_shape(series_shape),
        "g12": _jsonable_shape(series_shape),
        "B_k": _jsonable_shape(series_shape),
        "pressure_hessian_norm": _jsonable_shape(series_shape),
        "beta": [],
    }
    if include_velocity_hessian:
        shapes["velocity_hessian_norm_squared"] = _jsonable_shape(series_shape)
        shapes["strain_hessian_norm_squared"] = _jsonable_shape(series_shape)
        shapes["antisym_hessian_norm_squared"] = _jsonable_shape(series_shape)
    if output_time_shape is not None:
        shapes["time"] = _jsonable_shape(output_time_shape)
    return {
        "producer": PRODUCER_NAME,
        "status": "ok",
        "fail_closed": True,
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_keys": input_keys,
        "velocity_source": velocity_source,
        "velocity_keys": list(velocity_keys),
        "pressure_key": pressure_key,
        "pressure_mode": pressure_mode,
        "time_key": time_key,
        "axis_order": axis_order,
        "domain_length": float(domain_length),
        "domain_length_source": domain_length_source,
        "grid_spacing": float(grid_spacing),
        "N": int(n),
        "n_snapshots": int(series_shape[0]) if len(series_shape) == 4 else 1,
        "series_shape": _jsonable_shape(series_shape),
        "output_keys": output_keys,
        "output_shapes": shapes,
        "beta_value": float(beta_value),
        "notes": [
            "lambda2 is the second strain eigenvalue",
            "g12 is lambda2 - lambda1",
            "B_k is max_k 2|e1^T (partial_k S) e2|^2",
            "velocity_hessian_norm_squared = strain_hessian_norm_squared + antisym_hessian_norm_squared up to floating-point roundoff",
        ],
    }


def _write_npz_atomic(path: Path, payload: dict[str, Any]) -> None:
    path = _prepare_output_path(path)
    fd, tmp_name = tempfile.mkstemp(prefix=path.stem + ".", suffix=".npz", dir=str(path.parent))
    os.close(fd)
    try:
        with zipfile.ZipFile(tmp_name, mode="w", compression=zipfile.ZIP_STORED) as archive:
            for name, value in payload.items():
                buffer = io.BytesIO()
                np.save(buffer, np.asarray(value), allow_pickle=False)
                info = zipfile.ZipInfo(f"{name}.npy", date_time=(1980, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_STORED
                info.create_system = 0
                info.external_attr = 0o600 << 16
                archive.writestr(info, buffer.getvalue())
        os.replace(tmp_name, path)
    finally:
        if os.path.exists(tmp_name):
            try:
                os.unlink(tmp_name)
            except FileNotFoundError:
                pass


def _build_archive(args: argparse.Namespace) -> tuple[dict[str, Any], dict[str, Any]]:
    input_path = Path(args.input)
    if input_path.suffix.lower() != ".npz":
        raise ValueError("input path must be a .npz archive")
    if not input_path.exists():
        raise FileNotFoundError(f"input archive not found: {input_path}")

    data = _load_npz(input_path)
    if not data:
        raise ValueError("input archive is empty")

    input_keys = sorted(data.keys())
    u, v, w, velocity_keys, velocity_source = _load_velocity_components(data, args.snapshot_index)
    raw_axis_order, axis_name = _optional_text(data, "axis_order")
    axis_order = raw_axis_order.replace(" ", "") if raw_axis_order is not None else "x,y,z"
    if axis_order.endswith(",component"):
        axis_order = axis_order.removesuffix(",component")
    if axis_order not in VALID_AXIS_ORDERS:
        raise ValueError(f"{axis_name or 'axis_order'} must be one of {sorted(VALID_AXIS_ORDERS)!r}, got {axis_order!r}")

    u = _standardize_axis_order(u, axis_order)
    v = _standardize_axis_order(v, axis_order)
    w = _standardize_axis_order(w, axis_order)
    n = _validate_n(data, u.shape)
    u = _realize_array("u", u)
    v = _realize_array("v", v)
    w = _realize_array("w", w)

    # After normalization every field is stored in x,y,z order.
    time, time_key = _time_array(data, 1 if u.ndim == 3 else int(u.shape[0]))
    time = _time_for_snapshot(time, args.snapshot_index)
    if time is not None and time.ndim == 1 and time.shape[0] != (1 if u.ndim == 3 else int(u.shape[0])):
        raise ValueError("time metadata length does not match the velocity snapshots")

    pressure, pressure_key, pressure_kind = _load_optional_pressure(data, args.snapshot_index)
    if pressure is not None:
        pressure = _standardize_axis_order(pressure, axis_order)
        pressure = _realize_array("pressure", pressure)
        if pressure.shape != u.shape:
            raise ValueError(f"pressure shape {pressure.shape!r} does not match velocity shape {u.shape!r}")

    domain_length, domain_length_source = _validate_domain_length(data, n, args.domain_length)
    grid_spacing = domain_length / float(n)

    if u.shape[-3:] != (n, n, n):
        raise ValueError(f"velocity spatial shape {u.shape[-3:]!r} does not match N={n}")
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError(f"velocity component shapes differ after normalization: {u.shape!r}, {v.shape!r}, {w.shape!r}")

    n_snapshots = 1 if u.ndim == 3 else int(u.shape[0])
    if time is not None and time.ndim == 1 and len(time) != n_snapshots:
        raise ValueError(f"time length {len(time)} does not match the number of snapshots {n_snapshots}")

    grad = _velocity_gradient(u, v, w, domain_length)
    strain = _strain_tensor(grad)
    eigenvalues, eigenvectors = _strain_eigensystem(strain)
    lambda1 = np.asarray(eigenvalues[..., 0], dtype=np.float64)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    g12 = lambda2 - lambda1
    strain_gradient = _strain_gradient_tensor(strain, domain_length)
    B_k = _compute_B_k(eigenvectors, strain_gradient)

    pressure_mode = f"provided:{pressure_kind}" if pressure is not None else "poisson_recovered"
    if pressure is None:
        if args.allow_zero_pressure:
            pressure_hessian_norm = np.zeros_like(lambda2, dtype=np.float64)
            pressure_mode = "zero_fallback"
        else:
            divergence = grad[0, 0] + grad[1, 1] + grad[2, 2]
            divergence_max_abs = float(np.max(np.abs(divergence)))
            grad_max_abs = float(np.max(np.abs(grad)))
            div_limit = max(1.0e-12, DIV_TOL * max(1.0, grad_max_abs))
            if divergence_max_abs > div_limit:
                raise ValueError(
                    "pressure is absent and the velocity field is not sufficiently incompressible "
                    f"for Poisson recovery: max_abs_divergence={divergence_max_abs:.3e}, "
                    f"limit={div_limit:.3e}"
                )
            strain_norm_sq = _tensor_frobenius_squared(strain)
            omega_sq = np.sum(_vorticity_from_gradient(grad) ** 2, axis=0)
            rhs = strain_norm_sq - 0.5 * omega_sq
            pressure = _solve_periodic_poisson_negative_laplacian(rhs, domain_length)
            pressure_hessian_norm = _pressure_hessian_norm_from_pressure(pressure, domain_length)
            if not np.all(np.isfinite(pressure_hessian_norm)):
                raise ValueError("pressure recovery produced non-finite pressure_hessian_norm values")
    else:
        pressure_hessian_norm = _pressure_hessian_norm_from_pressure(pressure, domain_length)
        if not np.all(np.isfinite(pressure_hessian_norm)):
            raise ValueError("provided pressure produced non-finite pressure_hessian_norm values")

    beta_value = _beta_value(args)
    beta = np.array(beta_value, dtype=np.float64)

    output_payload: dict[str, Any] = {
        "lambda2": np.asarray(lambda2, dtype=np.float64),
        "g12": np.asarray(g12, dtype=np.float64),
        "B_k": np.asarray(B_k, dtype=np.float64),
        "pressure_hessian_norm": np.asarray(pressure_hessian_norm, dtype=np.float64),
        "beta": beta,
        "domain_length": np.array(domain_length, dtype=np.float64),
        "grid_spacing": np.array(grid_spacing, dtype=np.float64),
        "N": np.array(n, dtype=np.int64),
        "axis_order": np.array("x,y,z"),
        "velocity_source": np.array(velocity_source),
        "velocity_keys": np.array(",".join(velocity_keys)),
        "pressure_mode": np.array(pressure_mode),
        "input_path": np.array(str(input_path)),
        "producer": np.array(PRODUCER_NAME),
    }
    if args.include_velocity_hessian:
        strain_hessian_norm_squared = _matrix_gradient_norm_squared(strain_gradient, "strain_hessian_norm_squared")
        antisym_gradient = _matrix_gradient_tensor(_antisym_tensor(grad), domain_length, "antisymmetric velocity gradient")
        antisym_hessian_norm_squared = _matrix_gradient_norm_squared(antisym_gradient, "antisym_hessian_norm_squared")
        velocity_hessian_norm_squared = strain_hessian_norm_squared + antisym_hessian_norm_squared
        output_payload["velocity_hessian_norm_squared"] = np.asarray(velocity_hessian_norm_squared, dtype=np.float64)
        output_payload["strain_hessian_norm_squared"] = np.asarray(strain_hessian_norm_squared, dtype=np.float64)
        output_payload["antisym_hessian_norm_squared"] = np.asarray(antisym_hessian_norm_squared, dtype=np.float64)
    if args.snapshot_index is not None:
        output_payload["snapshot_index"] = np.array(args.snapshot_index, dtype=np.int64)

    output_time_shape: tuple[int, ...] | None = None
    if time is not None:
        output_payload["time"] = np.asarray(time)
        output_time_shape = tuple(int(dim) for dim in np.asarray(time).shape)
    elif "time" in data:
        raise ValueError("time metadata was present but could not be normalized")
    elif "t" in data:
        raise ValueError("t metadata was present but could not be normalized")

    manifest = _build_manifest(
        input_path=input_path,
        output_path=Path(args.output),
        input_keys=input_keys,
        velocity_source=velocity_source,
        velocity_keys=velocity_keys,
        pressure_key=pressure_key,
        pressure_mode=pressure_mode,
        time_key=time_key,
        axis_order="x,y,z",
        domain_length=domain_length,
        domain_length_source=domain_length_source,
        grid_spacing=grid_spacing,
        n=n,
        series_shape=tuple(int(dim) for dim in lambda2.shape),
        output_time_shape=output_time_shape,
        beta_value=beta_value,
        include_velocity_hessian=bool(args.include_velocity_hessian),
    )
    return output_payload, manifest


def _failure_manifest(args: argparse.Namespace, error: BaseException) -> dict[str, Any]:
    return {
        "producer": PRODUCER_NAME,
        "status": "error",
        "fail_closed": True,
        "input_path": str(args.input),
        "output_path": str(args.output),
        "beta_value": float(args.beta_value if args.beta_value is not None else DEFAULT_BETA_VALUE),
        "allow_zero_pressure": bool(args.allow_zero_pressure),
        "errors": [str(error)],
    }


def _minimal_failure_manifest(input_path: str | None, output_path: str | None, error_text: str) -> dict[str, Any]:
    return {
        "producer": PRODUCER_NAME,
        "status": "error",
        "fail_closed": True,
        "input_path": input_path,
        "output_path": output_path,
        "errors": [error_text],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", type=Path, required=True, help="input .npz archive with periodic velocity/pressure data")
    parser.add_argument("--output", type=Path, required=True, help="output derived .npz archive")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="override domain length metadata if the archive does not provide domain_length/length",
    )
    parser.add_argument(
        "--beta-value",
        type=float,
        default=None,
        help="scalar beta threshold to store in the derived archive; defaults to 0",
    )
    parser.add_argument(
        "--snapshot-index",
        type=int,
        default=None,
        help="derive one leading snapshot from velocity_snapshots/pressure_snapshots or 4D velocity fields",
    )
    parser.add_argument(
        "--allow-zero-pressure",
        action="store_true",
        help="store a zero pressure_hessian_norm field when pressure is absent and Poisson recovery is not used",
    )
    parser.add_argument(
        "--include-velocity-hessian",
        action="store_true",
        help=(
            "also materialize velocity_hessian_norm_squared plus the split "
            "strain_hessian_norm_squared and antisym_hessian_norm_squared fields"
        ),
    )
    args = parser.parse_args()
    args.output = _validate_output_path(args.output)
    if args.domain_length is not None:
        args.domain_length = _as_finite_real("--domain-length", args.domain_length)
        if args.domain_length <= 0.0:
            raise ValueError("--domain-length must be positive")
    if args.beta_value is not None:
        args.beta_value = _as_finite_real("--beta-value", args.beta_value)
    if args.snapshot_index is not None and args.snapshot_index < 0:
        raise ValueError("--snapshot-index must be nonnegative")
    return args


def main() -> None:
    args: argparse.Namespace | None = None
    try:
        args = parse_args()
        payload, manifest = _build_archive(args)
        _write_npz_atomic(args.output, payload)
    except SystemExit as exc:
        if getattr(exc, "code", None) == 0:
            raise
        error_text = f"argument parsing failed with exit code {getattr(exc, 'code', 1)}"
        manifest = (
            _failure_manifest(args, exc)
            if args is not None
            else _minimal_failure_manifest(None, None, error_text)
        )
        print(json.dumps(manifest, sort_keys=True, separators=(",", ":"), allow_nan=False))
        raise
    except Exception as exc:
        manifest = _failure_manifest(args, exc) if args is not None else _minimal_failure_manifest(None, None, str(exc))
        print(json.dumps(manifest, sort_keys=True, separators=(",", ":"), allow_nan=False))
        raise SystemExit(1) from exc

    print(json.dumps(manifest, sort_keys=True, separators=(",", ":"), allow_nan=False))


if __name__ == "__main__":
    main()
