#!/usr/bin/env python3
"""NS-GW-1 strain cross-derivative numerical diagnostic.

This script is an evidence-only numerical diagnostic for periodic 3D velocity
fields on ``[0, 2*pi)^3``.  It computes a selectable target strain eigenframe
and measures the local directional cross derivative ``d_{e1} d_{e2} lambda2``
of the intermediate strain eigenvalue field.  The legacy enstrophy-maximum
snapshot is still reported for backward compatibility.  With
``--kato-alignment`` it additionally reports Kato alignment quantities
including the condition
``B = 2 * <e2, (d_{e1} S) e1> * <e2, (d_{e2} S) e1>``.
With ``--integral-conditions`` it also reports weighted integral/average
diagnostics over vortex-support weights.
With ``--kato-stability-statistics`` it reports aggregate Kato mixed-plane
stability statistics over the whole ``lambda2<0`` region.

The built-in Taylor-Green field is synthetic.  A sign pass here is not DNS
evidence and is not a Navier-Stokes regularity proof.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np


DOMAIN_LENGTH = 2.0 * np.pi
CAVEAT = (
    "Synthetic Taylor-Green or user-supplied periodic-grid diagnostics are "
    "numerical evidence only; this is not DNS proof and not a Navier-Stokes "
    "regularity proof."
)
DNS_TIME_WINDOW_REQUIRED = "real_dns_t_approximately_7_to_9"
SIGN_TOLERANCE = 1.0e-12
JSON_FORMAT = "ns-gateway1-strain-cross-derivative-json-v1"
TARGET_MODES = (
    "enstrophy_max",
    "lambda2_min",
    "lambda2_negative_top_enstrophy",
    "strain_max",
)
XYZ_STORAGE_AXIS_CONVENTION = "numpy_array_axis_order:x,y,z"
ZYX_STORAGE_AXIS_CONVENTION = "numpy_array_axis_order:z,y,x"
AXIS_CONVENTION_TO_COORD_AXIS = {
    XYZ_STORAGE_AXIS_CONVENTION: (0, 1, 2),
    ZYX_STORAGE_AXIS_CONVENTION: (2, 1, 0),
}


def _as_real_array(name: str, value: Any) -> np.ndarray:
    array = np.asarray(value, dtype=float)
    if array.ndim != 3:
        raise ValueError(f"{name} must be a 3D array, got shape {array.shape!r}")
    if array.shape[0] != array.shape[1] or array.shape[1] != array.shape[2]:
        raise ValueError(f"{name} must be cubic, got shape {array.shape!r}")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def validate_velocity(u: Any, v: Any, w: Any) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Validate and return real cubic velocity component arrays."""

    ux = _as_real_array("u", u)
    vy = _as_real_array("v", v)
    wz = _as_real_array("w", w)
    if ux.shape != vy.shape or ux.shape != wz.shape:
        raise ValueError(f"velocity component shapes differ: {ux.shape}, {vy.shape}, {wz.shape}")
    return ux, vy, wz


def _optional_scalar(data: Any, name: str) -> float | int | str | None:
    if name not in data:
        return None
    value = np.asarray(data[name])
    if value.shape != ():
        raise ValueError(f"{name} metadata must be scalar, got shape {value.shape!r}")
    scalar = value.item()
    if isinstance(scalar, bytes):
        return scalar.decode("utf-8")
    if isinstance(scalar, np.generic):
        return scalar.item()
    return scalar


def _validate_npz_metadata(
    data: Any,
    n: int,
) -> dict[str, float | int | str]:
    metadata: dict[str, float | int | str] = {}

    declared_n = _optional_scalar(data, "N")
    if declared_n is not None:
        if int(declared_n) != declared_n:
            raise ValueError(f"N metadata must be an integer, got {declared_n!r}")
        if int(declared_n) != n:
            raise ValueError(f"N metadata {int(declared_n)} does not match velocity grid {n}")
        metadata["N"] = int(declared_n)

    domain_length = _optional_scalar(data, "domain_length")
    if domain_length is None:
        domain_length = _optional_scalar(data, "length")
    if domain_length is not None:
        length_value = float(domain_length)
        if not np.isfinite(length_value) or length_value <= 0.0:
            raise ValueError("domain_length metadata must be finite and positive")
        if not np.isclose(length_value, DOMAIN_LENGTH, rtol=1.0e-12, atol=1.0e-12):
            raise ValueError(
                "domain_length metadata must match the diagnostic domain "
                f"{DOMAIN_LENGTH:.17g}, got {length_value:.17g}"
            )
        metadata["domain_length"] = length_value

    grid_spacing = _optional_scalar(data, "grid_spacing")
    if grid_spacing is not None:
        spacing_value = float(grid_spacing)
        expected_spacing = DOMAIN_LENGTH / n
        if not np.isfinite(spacing_value) or spacing_value <= 0.0:
            raise ValueError("grid_spacing metadata must be finite and positive")
        if not np.isclose(spacing_value, expected_spacing, rtol=1.0e-12, atol=1.0e-12):
            raise ValueError(
                "grid_spacing metadata must match the diagnostic grid spacing "
                f"{expected_spacing:.17g}, got {spacing_value:.17g}"
            )
        metadata["grid_spacing"] = spacing_value

    amplitude = _optional_scalar(data, "amplitude")
    if amplitude is not None:
        amplitude_value = float(amplitude)
        if not np.isfinite(amplitude_value):
            raise ValueError("amplitude metadata must be finite")
        metadata["amplitude"] = amplitude_value

    for name in ("time", "snapshot_index"):
        value = _optional_scalar(data, name)
        if value is None:
            continue
        if name == "snapshot_index":
            if int(value) != value:
                raise ValueError(f"{name} metadata must be an integer, got {value!r}")
            metadata[name] = int(value)
        else:
            time_value = float(value)
            if not np.isfinite(time_value):
                raise ValueError(f"{name} metadata must be finite")
            metadata[name] = time_value

    source = _optional_scalar(data, "source")
    if source is not None:
        metadata["npz_source"] = str(source)

    axis_order = _optional_scalar(data, "axis_order")
    if axis_order is not None:
        axis_order_text = str(axis_order).replace(" ", "")
        if axis_order_text not in {"x,y,z", "z,y,x"}:
            raise ValueError(
                "axis_order metadata must be one of 'x,y,z' or 'z,y,x', "
                f"got {axis_order!r}"
            )
        metadata["axis_order"] = axis_order_text

    return metadata


def infer_axis_convention(
    source: str,
    field_metadata: dict[str, Any],
) -> str:
    """Return the physical-coordinate-to-array-axis convention for derivatives."""

    axis_order = field_metadata.get("axis_order")
    if axis_order == "x,y,z":
        return XYZ_STORAGE_AXIS_CONVENTION
    if axis_order == "z,y,x":
        return ZYX_STORAGE_AXIS_CONVENTION

    npz_source = str(field_metadata.get("npz_source", "")).lower()
    if "fluidsim" in npz_source:
        return ZYX_STORAGE_AXIS_CONVENTION
    if source.startswith("synthetic_"):
        return XYZ_STORAGE_AXIS_CONVENTION
    return XYZ_STORAGE_AXIS_CONVENTION


def coord_axis(axis_convention: str, coord: int) -> int:
    if axis_convention not in AXIS_CONVENTION_TO_COORD_AXIS:
        raise ValueError(f"unsupported axis convention: {axis_convention!r}")
    return AXIS_CONVENTION_TO_COORD_AXIS[axis_convention][coord]


def wavenumbers(n: int, length: float = DOMAIN_LENGTH) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return Fourier wavenumber grids for a cubic periodic domain."""

    if n < 4:
        raise ValueError("N must be at least 4")
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=length / n)
    return np.meshgrid(k, k, k, indexing="ij")


def spectral_derivative(
    field: np.ndarray,
    axis: int,
    length: float = DOMAIN_LENGTH,
    axis_convention: str = XYZ_STORAGE_AXIS_CONVENTION,
) -> np.ndarray:
    """Periodic spectral derivative of a scalar field along one axis."""

    scalar = _as_real_array("field", field)
    n = scalar.shape[0]
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=length / n)
    shape = [1, 1, 1]
    shape[coord_axis(axis_convention, axis)] = n
    multiplier = 1j * k.reshape(shape)
    return np.fft.ifftn(multiplier * np.fft.fftn(scalar)).real


def spectral_hessian(
    field: np.ndarray,
    length: float = DOMAIN_LENGTH,
    axis_convention: str = XYZ_STORAGE_AXIS_CONVENTION,
) -> np.ndarray:
    """Return Hessian H[i,j] = partial_i partial_j field via FFT."""

    scalar = _as_real_array("field", field)
    n = scalar.shape[0]
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=length / n)
    ks = []
    for coord in range(3):
        shape = [1, 1, 1]
        shape[coord_axis(axis_convention, coord)] = n
        ks.append(k.reshape(shape))
    field_hat = np.fft.fftn(scalar)
    hessian = np.empty((3, 3) + scalar.shape, dtype=float)
    for i in range(3):
        for j in range(3):
            hessian[i, j] = np.fft.ifftn(-(ks[i] * ks[j]) * field_hat).real
    return hessian


def strain_gradient_tensor(
    strain: np.ndarray,
    length: float = DOMAIN_LENGTH,
    axis_convention: str = XYZ_STORAGE_AXIS_CONVENTION,
) -> np.ndarray:
    """Return strain gradient tensor G[i,j,k] = ∂_k S_ij by FFT."""

    strain_tensor = np.asarray(strain, dtype=float)
    if strain_tensor.ndim != 5 or strain_tensor.shape[:2] != (3, 3):
        raise ValueError(
            f"strain must have shape (3,3,N,N,N), got {strain_tensor.shape!r}"
        )
    gradient = np.empty((3, 3, 3) + strain_tensor.shape[2:], dtype=float)
    for row in range(3):
        for col in range(3):
            for axis in range(3):
                gradient[row, col, axis] = spectral_derivative(
                    strain_tensor[row, col],
                    axis,
                    length,
                    axis_convention,
                )
    return gradient


def solve_periodic_poisson_negative_laplacian(
    rhs: np.ndarray,
    length: float = DOMAIN_LENGTH,
) -> np.ndarray:
    """Solve ``-Delta p = rhs`` on a periodic cube with zero-mean pressure."""

    source = _as_real_array("rhs", rhs)
    n = source.shape[0]
    kx, ky, kz = wavenumbers(n, length)
    k_squared = kx * kx + ky * ky + kz * kz
    rhs_hat = np.fft.fftn(source)
    pressure_hat = np.zeros_like(rhs_hat, dtype=complex)
    nonzero = k_squared > 0.0
    pressure_hat[nonzero] = rhs_hat[nonzero] / k_squared[nonzero]
    return np.fft.ifftn(pressure_hat).real


def velocity_gradient(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    length: float = DOMAIN_LENGTH,
    axis_convention: str = XYZ_STORAGE_AXIS_CONVENTION,
) -> np.ndarray:
    """Return grad[a,b] = partial_b velocity_a for a 3D periodic velocity."""

    ux, vy, wz = validate_velocity(u, v, w)
    components = (ux, vy, wz)
    grad = np.empty((3, 3) + ux.shape, dtype=float)
    for component_idx, component in enumerate(components):
        for axis in range(3):
            grad[component_idx, axis] = spectral_derivative(
                component,
                axis,
                length,
                axis_convention,
            )
    return grad


def strain_tensor(grad: np.ndarray) -> np.ndarray:
    """Return symmetric strain tensor field from a velocity gradient field."""

    gradient = np.asarray(grad, dtype=float)
    if gradient.ndim != 5 or gradient.shape[:2] != (3, 3):
        raise ValueError(f"grad must have shape (3,3,N,N,N), got {gradient.shape!r}")
    return 0.5 * (gradient + np.swapaxes(gradient, 0, 1))


def tensor_frobenius_squared(tensor: np.ndarray) -> np.ndarray:
    """Return pointwise Frobenius norm squared for a 3x3 tensor field."""

    tensor_field = np.asarray(tensor, dtype=float)
    if tensor_field.ndim != 5 or tensor_field.shape[:2] != (3, 3):
        raise ValueError(f"tensor must have shape (3,3,N,N,N), got {tensor_field.shape!r}")
    return np.sum(tensor_field * tensor_field, axis=(0, 1))


def vorticity_from_gradient(grad: np.ndarray) -> np.ndarray:
    """Return curl velocity as omega[component,x,y,z] from grad velocity."""

    gradient = np.asarray(grad, dtype=float)
    omega = np.empty((3,) + gradient.shape[2:], dtype=float)
    omega[0] = gradient[2, 1] - gradient[1, 2]
    omega[1] = gradient[0, 2] - gradient[2, 0]
    omega[2] = gradient[1, 0] - gradient[0, 1]
    return omega


def enstrophy_density(omega: np.ndarray) -> np.ndarray:
    """Return pointwise |omega|^2."""

    vort = np.asarray(omega, dtype=float)
    if vort.ndim != 4 or vort.shape[0] != 3:
        raise ValueError(f"omega must have shape (3,N,N,N), got {vort.shape!r}")
    return np.sum(vort * vort, axis=0)


def divergence_from_gradient(grad: np.ndarray) -> np.ndarray:
    """Return pointwise divergence from grad[a,b] = partial_b velocity_a."""

    gradient = np.asarray(grad, dtype=float)
    if gradient.ndim != 5 or gradient.shape[:2] != (3, 3):
        raise ValueError(f"grad must have shape (3,3,N,N,N), got {gradient.shape!r}")
    return gradient[0, 0] + gradient[1, 1] + gradient[2, 2]


def divergence_for_axis_convention(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    axis_convention: str,
) -> np.ndarray:
    """Return divergence after recomputing derivatives under an axis convention."""

    return divergence_from_gradient(
        velocity_gradient(u, v, w, axis_convention=axis_convention)
    )


def taylor_green_velocity(
    n: int,
    amplitude: float = 1.0,
    *,
    length: float = DOMAIN_LENGTH,
    time_scale: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Generate the standard 3D Taylor-Green velocity on ``[0, 2*pi)^3``.

    ``time_scale`` is a deterministic multiplicative scale, allowing callers to
    inject a simple time-like decay/amplification factor without changing the
    phase of the synthetic field.
    """

    if n < 4:
        raise ValueError("N must be at least 4")
    x = np.linspace(0.0, length, n, endpoint=False)
    X, Y, Z = np.meshgrid(x, x, x, indexing="ij")
    scale = float(amplitude) * float(time_scale)
    u = scale * np.sin(X) * np.cos(Y) * np.cos(Z)
    v = -scale * np.cos(X) * np.sin(Y) * np.cos(Z)
    w = np.zeros_like(u)
    return u, v, w


def load_velocity_npz(path: str | Path) -> tuple[np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    """Load velocity arrays named u, v, w and validated metadata from an NPZ file."""

    with np.load(Path(path)) as data:
        missing = [name for name in ("u", "v", "w") if name not in data]
        if missing:
            raise ValueError(f"field NPZ missing arrays: {', '.join(missing)}")
        u, v, w = validate_velocity(data["u"], data["v"], data["w"])
        metadata = _validate_npz_metadata(data, int(u.shape[0]))
        return u, v, w, metadata


def _tensor_at(tensor_field: np.ndarray, index: tuple[int, int, int]) -> np.ndarray:
    return np.asarray(tensor_field[(slice(None), slice(None)) + index], dtype=float)


def _directional_hessian_cross(
    hessian: np.ndarray,
    index: tuple[int, int, int],
    e1: np.ndarray,
    e2: np.ndarray,
) -> float:
    local_hessian = _tensor_at(hessian, index)
    return float(e1 @ local_hessian @ e2)


def _directional_strain_gradient_projection(
    strain_gradient: np.ndarray,
    index: tuple[int, int, int],
    left_vector: np.ndarray,
    right_vector: np.ndarray,
    derivative_direction: np.ndarray,
) -> float:
    local_gradient = np.asarray(
        strain_gradient[(slice(None), slice(None), slice(None)) + index],
        dtype=float,
    )
    directional_matrix = np.tensordot(derivative_direction, local_gradient, axes=(0, 2))
    return float(left_vector @ (directional_matrix @ right_vector))


def _directional_strain_gradient_vector(
    strain_gradient: np.ndarray,
    index: tuple[int, int, int],
    derivative_direction: np.ndarray,
    right_vector: np.ndarray,
) -> np.ndarray:
    local_gradient = np.asarray(
        strain_gradient[(slice(None), slice(None), slice(None)) + index],
        dtype=float,
    )
    directional_matrix = np.tensordot(derivative_direction, local_gradient, axes=(0, 2))
    return np.asarray(directional_matrix @ right_vector, dtype=float)


def _project_hessian_to_eigenframe(
    hessian: np.ndarray,
    eigenframe: np.ndarray,
) -> np.ndarray:
    """Project a symmetric 3x3 Hessian matrix into a local eigenframe basis."""

    local_hessian = np.asarray(hessian, dtype=float)
    basis = np.asarray(eigenframe, dtype=float)
    if local_hessian.shape != (3, 3):
        raise ValueError(f"hessian must be shape (3, 3), got {local_hessian.shape!r}")
    if basis.shape != (3, 3):
        raise ValueError(f"eigenframe must be shape (3, 3), got {basis.shape!r}")
    return basis.T @ local_hessian @ basis


def _weighted_field_statistics(
    field: np.ndarray,
    weights: np.ndarray,
    cell_volume: float,
) -> dict[str, float | None]:
    values = np.asarray(field, dtype=float)
    weight_array = np.asarray(weights, dtype=float)
    if values.shape != weight_array.shape:
        raise ValueError(
            f"weighted statistics field and weights must match, got {values.shape!r} and {weight_array.shape!r}"
        )
    weight_sum = float(np.sum(weight_array))
    weighted_sum = float(np.sum(values * weight_array))
    return {
        "weight_sum": weight_sum,
        "weight_integral": weight_sum * cell_volume,
        "weighted_sum": weighted_sum,
        "weighted_integral": weighted_sum * cell_volume,
        "weighted_average": weighted_sum / weight_sum if weight_sum > 0.0 else None,
    }


def _canonicalize_eigenvectors(eigenvectors: np.ndarray) -> np.ndarray:
    """Make eigenvector signs deterministic for stable JSON output."""

    vectors = np.array(eigenvectors, dtype=float, copy=True)
    for col in range(vectors.shape[1]):
        pivot = int(np.argmax(np.abs(vectors[:, col])))
        if vectors[pivot, col] < 0.0:
            vectors[:, col] *= -1.0
    return vectors


def _strain_eigenvalues_field(strain: np.ndarray) -> np.ndarray:
    matrices = np.moveaxis(strain, (0, 1), (-2, -1))
    return np.linalg.eigvalsh(matrices)


def _jsonify_vector(vector: np.ndarray) -> list[float]:
    return [float(x) for x in np.asarray(vector, dtype=float)]


def _jsonify_matrix(matrix: np.ndarray) -> list[list[float]]:
    array = np.asarray(matrix, dtype=float)
    return [[float(x) for x in row] for row in array]


def _target_snapshot_payload(
    *,
    target_index: tuple[int, int, int],
    target_enstrophy: float,
    target_strain_norm_squared: float,
    target_eigenvalues: np.ndarray,
    target_eigenvectors: np.ndarray,
    target_min_local_eigenvalue_gap: float,
    target_eigenframe_degenerate: bool,
    target_lambda2: float,
    target_cross_derivative: float,
    target_pressure_hessian_e1_e2: float,
) -> dict[str, Any]:
    """Return the selected target-point JSON payload with stable aliases."""

    return {
        "target_index": list(target_index),
        "target_enstrophy": float(target_enstrophy),
        "target_strain_norm_squared": float(target_strain_norm_squared),
        "target_eigenvalues": _jsonify_vector(target_eigenvalues),
        "target_eigenvectors": _jsonify_matrix(target_eigenvectors),
        "target_min_local_eigenvalue_gap": float(target_min_local_eigenvalue_gap),
        "target_eigenframe_degenerate": bool(target_eigenframe_degenerate),
        "target_lambda2": float(target_lambda2),
        "lambda2_at_target": float(target_lambda2),
        "target_cross_derivative_e1_e2_lambda2": float(target_cross_derivative),
        "cross_derivative_e1_e2_lambda2_at_target": float(target_cross_derivative),
        "target_pressure_hessian_e1_e2": float(target_pressure_hessian_e1_e2),
        "pressure_hessian_e1_e2_at_target": float(target_pressure_hessian_e1_e2),
    }


def _finite_quantiles(values: np.ndarray) -> dict[str, float | None]:
    finite = np.asarray(values, dtype=float)
    finite = finite[np.isfinite(finite)]
    if finite.size == 0:
        return {
            "min": None,
            "p05": None,
            "p25": None,
            "median": None,
            "p75": None,
            "p95": None,
            "max": None,
        }
    quantiles = np.quantile(finite, [0.0, 0.05, 0.25, 0.5, 0.75, 0.95, 1.0])
    return {
        "min": float(quantiles[0]),
        "p05": float(quantiles[1]),
        "p25": float(quantiles[2]),
        "median": float(quantiles[3]),
        "p75": float(quantiles[4]),
        "p95": float(quantiles[5]),
        "max": float(quantiles[6]),
    }


def _kato_stability_statistics(
    *,
    strain: np.ndarray,
    strain_gradient: np.ndarray,
    lambda2_field: np.ndarray,
    lambda2_hessian: np.ndarray,
    lambda2_min: float,
    kato_beta_threshold: float | None = None,
) -> dict[str, Any]:
    """Aggregate mixed-plane Kato stability statistics over ``lambda2<0``.

    For each nondegenerate point with ``lambda2<0`` this uses the mixed
    ``e1/e2`` decomposition

        cross = B / gap12 + remainder

    where ``B = 2 * <e2,(d_e1 S)e1> * <e2,(d_e2 S)e1>``.  The reported
    ``kappa_abs`` is ``abs(B/gap12) / abs(remainder)``.  This is an empirical
    shape statistic only; it is not a regularity criterion.
    """

    if lambda2_hessian.shape[:2] != (3, 3):
        raise ValueError(f"lambda2_hessian must be shape (3,3,N,N,N), got {lambda2_hessian.shape!r}")
    if not np.isfinite(lambda2_min):
        raise ValueError(f"lambda2_min must be finite, got {lambda2_min!r}")

    matrices = np.moveaxis(strain, (0, 1), (-2, -1))
    eigenvalues, eigenvectors = np.linalg.eigh(matrices)
    mask = lambda2_field < 0.0
    negative_count = int(np.count_nonzero(mask))
    beta = (
        float(kato_beta_threshold * lambda2_min)
        if kato_beta_threshold is not None
        else None
    )
    if beta is not None:
        omega_beta_mask = lambda2_field <= beta
        omega_beta_count = int(np.count_nonzero(omega_beta_mask))
    else:
        omega_beta_count = negative_count
    if negative_count == 0:
        total_points = int(lambda2_field.size)
        lambda2_negative_fraction = 0.0
        omega_beta_fraction = float(omega_beta_count / total_points) if total_points > 0 else 0.0
        omega_K_inside_Omega_beta_count = 0
        omega_K_inside_Omega_beta_fraction = (
            float(omega_K_inside_Omega_beta_count / omega_beta_count)
            if omega_beta_count > 0
            else None
        )
        omega_K_inside_Omega_beta_fraction_on_domain = (
            float(omega_K_inside_Omega_beta_count / total_points) if total_points > 0 else 0.0
        )
        beta_metrics: dict[str, Any] = {}
        if beta is not None:
            beta_metrics = {
                "kato_stability_omega_K_inside_Omega_beta_count": omega_K_inside_Omega_beta_count,
                "kato_stability_omega_K_inside_Omega_beta_fraction": omega_K_inside_Omega_beta_fraction,
                "kato_stability_omega_K_inside_Omega_beta_fraction_on_domain": (
                    omega_K_inside_Omega_beta_fraction_on_domain
                ),
                "kato_stability_omega_beta_threshold": float(kato_beta_threshold),
                "kato_stability_omega_beta_threshold_lambda2_min": float(lambda2_min),
                "kato_stability_omega_beta_threshold_beta": float(beta),
                "kato_stability_beta_threshold": float(kato_beta_threshold),
                "kato_stability_beta_threshold_lambda2_min": float(lambda2_min),
                "kato_stability_beta_threshold_beta": float(beta),
            }
        return {
            "kato_stability_statistics_enabled": True,
            "kato_stability_region": "lambda2<0",
            "kato_stability_total_points": total_points,
            "kato_stability_point_count_total": total_points,
            "kato_stability_omega_beta_count": omega_beta_count,
            "kato_stability_omega_K_count": 0,
            "kato_stability_Omega_beta_fraction": omega_beta_fraction,
            "kato_stability_lambda2_negative_fraction": lambda2_negative_fraction,
            "kato_stability_omega_tube_fraction": 0.0,
            "kato_stability_cross_derivative_positive_count": 0,
            "kato_stability_cross_derivative_positive_fraction": None,
            "kato_stability_cross_derivative_positive_fraction_on_domain": 0.0,
            "kato_stability_cross_derivative_positive_fraction_on_lambda2_negative": 0.0,
            "kato_stability_cross_derivative_fractionally_stable_in_lambda2": 0.0,
            "kato_stability_omega_K_fraction": 0.0,
            "kato_stability_point_count": 0,
            "kato_stability_nonfinite_or_degenerate_count": 0,
            "kato_stability_finite_count": 0,
            **beta_metrics,
            "kato_stability_blocker": "lambda2<0 region is empty",
        }

    gap12 = eigenvalues[..., 1] - eigenvalues[..., 0]
    negative_indices = np.argwhere(mask)
    kappa_abs_values: list[float] = []
    kappa_signed_values: list[float] = []
    b_over_gap12_values: list[float] = []
    remainder_values: list[float] = []
    cross_values: list[float] = []
    lambda2_values: list[float] = []
    b_positive_count = 0
    omega_K_count = 0
    omega_K_inside_Omega_beta_count = 0
    degenerate_or_nonfinite_count = 0

    for raw_index in negative_indices:
        index = tuple(int(i) for i in raw_index)
        local_gap12 = float(gap12[index])
        if not np.isfinite(local_gap12) or abs(local_gap12) <= 1.0e-10:
            degenerate_or_nonfinite_count += 1
            continue
        local_vectors = np.asarray(eigenvectors[index], dtype=float)
        local_vectors = _canonicalize_eigenvectors(local_vectors)
        e1 = local_vectors[:, 0]
        e2 = local_vectors[:, 1]
        cross = _directional_hessian_cross(lambda2_hessian, index, e1, e2)
        e2_d_e1S_e1 = _directional_strain_gradient_projection(
            strain_gradient,
            index,
            e2,
            e1,
            e1,
        )
        e2_d_e2S_e1 = _directional_strain_gradient_projection(
            strain_gradient,
            index,
            e2,
            e1,
            e2,
        )
        kato_b = 2.0 * e2_d_e1S_e1 * e2_d_e2S_e1
        b_over_gap12 = kato_b / local_gap12
        remainder = cross - b_over_gap12
        if not (
            np.isfinite(cross)
            and np.isfinite(kato_b)
            and np.isfinite(b_over_gap12)
            and np.isfinite(remainder)
        ):
            degenerate_or_nonfinite_count += 1
            continue
        if cross > SIGN_TOLERANCE:
            omega_K_count += 1
            if beta is not None and float(lambda2_field[index]) <= beta:
                omega_K_inside_Omega_beta_count += 1
        if kato_b > 0.0:
            b_positive_count += 1
        if abs(remainder) <= SIGN_TOLERANCE:
            kappa_abs = np.inf
            kappa_signed = np.inf if b_over_gap12 >= 0.0 else -np.inf
        else:
            kappa_abs = abs(b_over_gap12) / abs(remainder)
            kappa_signed = b_over_gap12 / abs(remainder)
        kappa_abs_values.append(float(kappa_abs))
        kappa_signed_values.append(float(kappa_signed))
        b_over_gap12_values.append(float(b_over_gap12))
        remainder_values.append(float(remainder))
        cross_values.append(float(cross))
        lambda2_values.append(float(lambda2_field[index]))

    kappa_abs_array = np.asarray(kappa_abs_values, dtype=float)
    kappa_signed_array = np.asarray(kappa_signed_values, dtype=float)
    finite_count = int(np.count_nonzero(np.isfinite(kappa_abs_array)))
    valid_count = int(kappa_abs_array.size)
    cross_derivative_positive_count = int(omega_K_count)
    if valid_count == 0:
        fraction_abs_gt_1 = None
        fraction_signed_gt_1 = None
        fraction_b_positive = None
        fraction_cross_derivative_positive = None
        fraction_cross_derivative_positive_on_lambda2_negative = None
    else:
        fraction_abs_gt_1 = float(np.count_nonzero(kappa_abs_array > 1.0) / valid_count)
        fraction_signed_gt_1 = float(np.count_nonzero(kappa_signed_array > 1.0) / valid_count)
        fraction_b_positive = float(b_positive_count / valid_count)
        fraction_cross_derivative_positive = float(cross_derivative_positive_count / valid_count)
        fraction_cross_derivative_positive_on_lambda2_negative = float(
            cross_derivative_positive_count / negative_count
        )

    total_points = int(lambda2_field.size)
    lambda2_negative_fraction = float(negative_count / total_points) if total_points > 0 else 0.0
    omega_tube_fraction = float(omega_K_count / total_points) if total_points > 0 else 0.0
    cross_derivative_positive_fraction_on_domain = (
        float(cross_derivative_positive_count / total_points) if total_points > 0 else 0.0
    )
    fraction_omega_tube = (
        float(omega_K_count / negative_count) if negative_count > 0 else 0.0
    )
    omega_K_inside_Omega_beta_fraction = (
        float(omega_K_inside_Omega_beta_count / omega_beta_count)
        if omega_beta_count > 0
        else None
    )
    omega_K_inside_Omega_beta_fraction_on_domain = (
        float(omega_K_inside_Omega_beta_count / total_points) if total_points > 0 else 0.0
    )
    omega_beta_fraction = float(omega_beta_count / total_points) if total_points > 0 else 0.0
    beta_metrics: dict[str, Any] = {}
    if beta is not None:
        beta_metrics = {
            "kato_stability_omega_K_inside_Omega_beta_count": omega_K_inside_Omega_beta_count,
            "kato_stability_omega_K_inside_Omega_beta_fraction": omega_K_inside_Omega_beta_fraction,
            "kato_stability_omega_K_inside_Omega_beta_fraction_on_domain": (
                omega_K_inside_Omega_beta_fraction_on_domain
            ),
            "kato_stability_omega_beta_threshold": float(kato_beta_threshold),
            "kato_stability_omega_beta_threshold_lambda2_min": float(lambda2_min),
            "kato_stability_omega_beta_threshold_beta": float(beta),
            "kato_stability_beta_threshold": float(kato_beta_threshold),
            "kato_stability_beta_threshold_lambda2_min": float(lambda2_min),
            "kato_stability_beta_threshold_beta": float(beta),
        }

    return {
        "kato_stability_statistics_enabled": True,
        "kato_stability_region": "lambda2<0",
        "kato_stability_formula": "cross_e1e2_lambda2 = B/gap12 + remainder; kappa_abs = abs(B/gap12)/abs(remainder)",
        "kato_stability_total_points": total_points,
        "kato_stability_point_count_total": total_points,
        "kato_stability_omega_beta_count": omega_beta_count,
        "kato_stability_omega_K_count": omega_K_count,
        "kato_stability_lambda2_negative_fraction": lambda2_negative_fraction,
        "kato_stability_omega_tube_fraction": omega_tube_fraction,
        "kato_stability_cross_derivative_positive_fraction_on_domain": cross_derivative_positive_fraction_on_domain,
        "kato_stability_cross_derivative_positive_fraction": fraction_cross_derivative_positive,
        "kato_stability_cross_derivative_positive_count": cross_derivative_positive_count,
        "kato_stability_cross_derivative_positive_fraction_on_lambda2_negative": (
            fraction_cross_derivative_positive_on_lambda2_negative
        ),
        "kato_stability_cross_derivative_fractionally_stable_in_lambda2": fraction_omega_tube,
        "kato_stability_kappa_abs_gt_1_denominator": valid_count,
        "kato_stability_kappa_signed_gt_1_denominator": valid_count,
        "kato_stability_point_count": negative_count,
        "kato_stability_nonfinite_or_degenerate_count": degenerate_or_nonfinite_count,
        "kato_stability_valid_count": valid_count,
        "kato_stability_finite_count": finite_count,
        "kato_stability_fraction_kappa_abs_gt_1": fraction_abs_gt_1,
        "kato_stability_fraction_kappa_signed_gt_1": fraction_signed_gt_1,
        "kato_stability_fraction_B_positive": fraction_b_positive,
        "kato_stability_omega_K_fraction": fraction_omega_tube,
        "kato_stability_Omega_beta_fraction": omega_beta_fraction,
        **beta_metrics,
        "kato_stability_kappa_abs_quantiles": _finite_quantiles(kappa_abs_array),
        "kato_stability_kappa_signed_quantiles": _finite_quantiles(kappa_signed_array),
        "kato_stability_B_over_gap12_quantiles": _finite_quantiles(
            np.asarray(b_over_gap12_values, dtype=float)
        ),
        "kato_stability_remainder_quantiles": _finite_quantiles(
            np.asarray(remainder_values, dtype=float)
        ),
        "kato_stability_cross_derivative_quantiles": _finite_quantiles(
            np.asarray(cross_values, dtype=float)
        ),
        "kato_stability_lambda2_quantiles": _finite_quantiles(
            np.asarray(lambda2_values, dtype=float)
        ),
    }


def classify_sign(value: float, *, tolerance: float = SIGN_TOLERANCE) -> str:
    """Classify the local cross-derivative sign for JSON decision output."""

    if not np.isfinite(value):
        raise ValueError("sign classification value must be finite")
    if value > tolerance:
        return "positive_adverse_to_nonpositive_rule"
    if value < -tolerance:
        return "negative_supports_nonpositive_rule"
    return "zero_within_tolerance"


def format_summary(result: dict[str, Any]) -> str:
    """Return a compact human-readable summary for CLI logs."""

    source = str(result["source"])
    target_mode = str(result["target_mode"])
    target_index = tuple(result["target_index"])
    target_cross = float(result["target_cross_derivative_e1_e2_lambda2"])
    classification = str(result["sign_classification"])
    target_classification = str(result.get("target_sign_classification", result["sign_classification"]))
    status = str(result["diagnostic_status"])
    artifact = result.get("result_artifact_path")
    artifact_text = f", artifact={artifact}" if artifact else ""
    target_status = result.get("target_diagnostic_status")
    target_status_text = f", target_status={target_status}" if target_status else ""
    integral_conditions = ""
    if result.get("integral_conditions_enabled"):
        percentile = result.get("integral_conditions_top_enstrophy_percentile")
        if percentile is None:
            integral_conditions = ", integral_conditions=on"
        else:
            integral_conditions = f", integral_conditions=on(top_enstrophy_percentile={percentile})"
    kato_alignment = ""
    if result.get("kato_alignment_enabled"):
        kato_alignment = (
            f", kato_B={float(result['kato_alignment_B']):.17g}, "
            f"kato_B_sign={str(result['kato_alignment_B_sign'])}"
        )
    return (
        "NS-GW-1 diagnostic: "
        f"source={source}, N={int(result['grid_N'])}, "
        f"target_mode={target_mode}, target_index={target_index}, "
        f"target_d_e1_d_e2_lambda2={target_cross:.17g}, "
        f"classification={classification}, "
        f"target_classification={target_classification}, "
        f"enstrophy_max_index={tuple(result['enstrophy_max_index'])}, "
        f"status={status}{target_status_text}{artifact_text}{integral_conditions}{kato_alignment}"
    )


def _select_target_index(
    *,
    target_mode: str,
    enstrophy: np.ndarray,
    lambda2_field: np.ndarray,
    strain_norm_squared: np.ndarray,
    target_top_enstrophy_percentile: float,
) -> dict[str, Any]:
    """Select the diagnostic target point and record how it was chosen."""

    if target_mode == "enstrophy_max":
        flat_index = int(np.argmax(enstrophy))
        return {
            "target_index": tuple(int(i) for i in np.unravel_index(flat_index, enstrophy.shape)),
            "target_selection_status": "selected_enstrophy_max",
            "target_selection_blocker": None,
            "target_top_enstrophy_percentile": float(target_top_enstrophy_percentile),
            "target_top_enstrophy_threshold": None,
        }

    if target_mode == "lambda2_min":
        flat_index = int(np.argmin(lambda2_field))
        return {
            "target_index": tuple(int(i) for i in np.unravel_index(flat_index, lambda2_field.shape)),
            "target_selection_status": "selected_lambda2_min",
            "target_selection_blocker": None,
            "target_top_enstrophy_percentile": float(target_top_enstrophy_percentile),
            "target_top_enstrophy_threshold": None,
        }

    if target_mode == "strain_max":
        flat_index = int(np.argmax(strain_norm_squared))
        return {
            "target_index": tuple(int(i) for i in np.unravel_index(flat_index, strain_norm_squared.shape)),
            "target_selection_status": "selected_strain_max",
            "target_selection_blocker": None,
            "target_top_enstrophy_percentile": float(target_top_enstrophy_percentile),
            "target_top_enstrophy_threshold": None,
        }

    if target_mode == "lambda2_negative_top_enstrophy":
        enstrophy_threshold = float(np.percentile(enstrophy, target_top_enstrophy_percentile))
        top_enstrophy_mask = enstrophy >= enstrophy_threshold
        negative_mask = top_enstrophy_mask & (lambda2_field < 0.0)
        if np.any(negative_mask):
            masked_lambda2 = np.where(negative_mask, lambda2_field, np.inf)
            flat_index = int(np.argmin(masked_lambda2))
            status = "selected_negative_lambda2_within_top_enstrophy_mask"
            blocker = None
        else:
            masked_lambda2 = np.where(top_enstrophy_mask, lambda2_field, np.inf)
            flat_index = int(np.argmin(masked_lambda2))
            status = "fallback_most_negative_lambda2_in_top_enstrophy_mask"
            blocker = (
                "no lambda2<0 point in the top-enstrophy mask; fell back to the "
                "most negative lambda2 in the top-enstrophy mask"
            )
        return {
            "target_index": tuple(int(i) for i in np.unravel_index(flat_index, lambda2_field.shape)),
            "target_selection_status": status,
            "target_selection_blocker": blocker,
            "target_top_enstrophy_percentile": float(target_top_enstrophy_percentile),
            "target_top_enstrophy_threshold": enstrophy_threshold,
            "target_top_enstrophy_mask_count": int(np.count_nonzero(top_enstrophy_mask)),
            "target_negative_lambda2_top_mask_count": int(np.count_nonzero(negative_mask)),
        }

    raise ValueError(
        "target must be one of 'enstrophy_max', 'lambda2_min', "
        "'lambda2_negative_top_enstrophy', or 'strain_max'"
    )


def _diagnostic_status(
    *,
    source: str,
    field_metadata: dict[str, Any],
    eigenframe_degenerate: bool,
    sign_classification: str,
) -> tuple[str, bool, str]:
    source_is_synthetic = source == "synthetic_taylor_green"
    time_value = field_metadata.get("time")
    source_is_t0_fixture = time_value is not None and np.isclose(float(time_value), 0.0)
    zero_or_noise = sign_classification == "zero_within_tolerance"

    if eigenframe_degenerate and (source_is_synthetic or source_is_t0_fixture):
        blocker = (
            "t=0 synthetic/fixture eigenframe_degenerate=true; zero/noise cross "
            "derivative is not evidence for sign"
        )
        return "fail_closed_degenerate_t0_not_sign_evidence", False, blocker

    if eigenframe_degenerate:
        blocker = "eigenframe_degenerate=true; eigenframe-local sign evidence is blocked"
        return "fail_closed_degenerate_eigenframe", False, blocker

    if source_is_synthetic:
        blocker = "synthetic Taylor-Green diagnostic is not DNS sign evidence"
        return "fail_closed_synthetic_not_dns_evidence", False, blocker

    if zero_or_noise:
        blocker = "zero/noise cross derivative is not sign evidence"
        return "fail_closed_zero_or_noise_not_sign_evidence", False, blocker

    blocker = f"{DNS_TIME_WINDOW_REQUIRED} still required before sign promotion"
    return "fail_closed_real_dns_window_required", False, blocker


def run_diagnostic(
    N: int = 32,
    amplitude: float = 1.0,
    field: str | Path | None = None,
    output: str | Path | None = None,
    target: str = "enstrophy_max",
    target_top_enstrophy_percentile: float = 90.0,
    integral_conditions: bool = False,
    top_enstrophy_percentile: float | None = None,
    kato_alignment: bool = False,
    kato_stability_statistics: bool = False,
    kato_beta_threshold: float | None = None,
    hessian_full_3d: bool = False,
) -> dict[str, Any]:
    """Run the NS-GW-1 diagnostic and return a JSON-serializable dict.

    ``field`` is an optional ``.npz`` path containing cubic 3D arrays named
    ``u``, ``v``, and ``w`` sampled on ``[0, 2*pi)^3``.  ``N`` and
    ``amplitude`` control only the deterministic built-in Taylor-Green field.
    ``target`` selects the local point used for the target-dependent
    diagnostics.  When ``integral_conditions`` is true, additional weighted
    integral and average diagnostics are reported over natural vortex support
    weights.  When ``kato_alignment`` is true, scalar projections defining
    Kato condition B are added at the selected target point.  When
    ``kato_stability_statistics`` is true, aggregate Kato mixed-plane
    statistics are reported over the whole ``lambda2<0`` region.  When
    ``kato_beta_threshold`` is provided, with ``0 < theta < 1``, bounded
    counts for the region ``lambda2 <= beta`` are emitted where
    ``beta = theta * lambda2_min``.  When
    ``hessian_full_3d`` is true, the full Hessian of lambda2 at the selected
    target point is projected into that target's strain eigenframe and its full
    3x3 entries/eigen-data are reported, including ratio-style confinement
    scales (``length^2`` and ``length``) and principal Taylor semi-axis estimates.
    """

    if int(N) != N:
        raise ValueError(f"N must be an integer, got {N!r}")
    N = int(N)
    amplitude = float(amplitude)
    if not np.isfinite(amplitude):
        raise ValueError("amplitude must be finite")
    if target not in TARGET_MODES:
        raise ValueError(
            "target must be one of 'enstrophy_max', 'lambda2_min', "
            "'lambda2_negative_top_enstrophy', or 'strain_max'"
        )
    target_top_enstrophy_percentile = float(target_top_enstrophy_percentile)
    if not np.isfinite(target_top_enstrophy_percentile):
        raise ValueError("target_top_enstrophy_percentile must be finite")
    if not (0.0 < target_top_enstrophy_percentile <= 100.0):
        raise ValueError("target_top_enstrophy_percentile must be in the interval (0, 100]")
    if top_enstrophy_percentile is not None:
        top_enstrophy_percentile = float(top_enstrophy_percentile)
        if not np.isfinite(top_enstrophy_percentile):
            raise ValueError("top_enstrophy_percentile must be finite")
        if not (0.0 < top_enstrophy_percentile <= 100.0):
            raise ValueError("top_enstrophy_percentile must be in the interval (0, 100]")
    if kato_beta_threshold is not None:
        kato_beta_threshold = float(kato_beta_threshold)
        if not np.isfinite(kato_beta_threshold):
            raise ValueError("--kato-beta-threshold / kato_beta_threshold must be finite")
        if not (0.0 < kato_beta_threshold < 1.0):
            raise ValueError("--kato-beta-threshold / kato_beta_threshold must be in the interval (0, 1)")

    field_metadata: dict[str, Any] = {}
    if field is not None:
        u, v, w, field_metadata = load_velocity_npz(field)
        source = f"npz:{Path(field)}"
    else:
        u, v, w = taylor_green_velocity(N, amplitude)
        source = "synthetic_taylor_green"

    n = int(u.shape[0])
    grid_spacing = float(DOMAIN_LENGTH / n)
    derivative_axis_convention = infer_axis_convention(source, field_metadata)
    grad = velocity_gradient(u, v, w, axis_convention=derivative_axis_convention)
    divergence = divergence_from_gradient(grad)
    divergence_xyz_storage = divergence_for_axis_convention(
        u, v, w, XYZ_STORAGE_AXIS_CONVENTION
    )
    divergence_zyx_storage = divergence_for_axis_convention(
        u, v, w, ZYX_STORAGE_AXIS_CONVENTION
    )
    strain = strain_tensor(grad)
    omega = vorticity_from_gradient(grad)
    strain_norm_squared = tensor_frobenius_squared(strain)
    enstrophy = enstrophy_density(omega)
    pressure_poisson_rhs = strain_norm_squared - 0.5 * enstrophy
    pressure = solve_periodic_poisson_negative_laplacian(pressure_poisson_rhs)

    max_flat = int(np.argmax(enstrophy))
    max_index = tuple(int(i) for i in np.unravel_index(max_flat, enstrophy.shape))

    local_strain = _tensor_at(strain, max_index)
    local_eigenvalues, local_eigenvectors = np.linalg.eigh(local_strain)
    local_eigenvectors = _canonicalize_eigenvectors(local_eigenvectors)
    lambda2 = float(local_eigenvalues[1])
    eigenvalue_gaps = np.diff(local_eigenvalues)
    min_eigenvalue_gap = float(np.min(np.abs(eigenvalue_gaps)))
    eigenframe_degenerate = bool(min_eigenvalue_gap <= 1.0e-10)
    e1 = local_eigenvectors[:, 0]
    e2 = local_eigenvectors[:, 1]

    eigenvalues_field = _strain_eigenvalues_field(strain)
    lambda2_field = eigenvalues_field[..., 1]
    lambda2_gradient = np.stack(
        [
            spectral_derivative(
                lambda2_field,
                axis,
                axis_convention=derivative_axis_convention,
            )
            for axis in range(3)
        ],
        axis=0,
    )
    hessian = spectral_hessian(
        lambda2_field,
        axis_convention=derivative_axis_convention,
    )
    lambda2_min = float(np.min(lambda2_field))
    pressure_hessian = spectral_hessian(pressure, axis_convention=derivative_axis_convention)
    target_selection = _select_target_index(
        target_mode=target,
        enstrophy=enstrophy,
        lambda2_field=lambda2_field,
        strain_norm_squared=strain_norm_squared,
        target_top_enstrophy_percentile=target_top_enstrophy_percentile,
    )
    target_index = tuple(int(i) for i in target_selection["target_index"])
    target_local_strain = _tensor_at(strain, target_index)
    target_eigenvalues, target_eigenvectors = np.linalg.eigh(target_local_strain)
    target_eigenvectors = _canonicalize_eigenvectors(target_eigenvectors)
    target_lambda2 = float(target_eigenvalues[1])
    target_eigenvalue_gaps = np.diff(target_eigenvalues)
    target_min_eigenvalue_gap = float(np.min(np.abs(target_eigenvalue_gaps)))
    target_eigenframe_degenerate = bool(target_min_eigenvalue_gap <= 1.0e-10)
    target_e1 = target_eigenvectors[:, 0]
    target_e2 = target_eigenvectors[:, 1]
    target_cross_derivative = _directional_hessian_cross(hessian, target_index, target_e1, target_e2)
    target_pressure_hessian_e1_e2 = _directional_hessian_cross(
        pressure_hessian,
        target_index,
        target_e1,
        target_e2,
    )
    target_sign_classification = classify_sign(target_cross_derivative)
    target_diagnostic_status, target_sign_evidence_for_promotion, target_sign_evidence_blocker = _diagnostic_status(
        source=source,
        field_metadata=field_metadata,
        eigenframe_degenerate=target_eigenframe_degenerate,
        sign_classification=target_sign_classification,
    )

    target_hessian_full_3d: dict[str, Any] = {
        "hessian_full_3d_enabled": False,
    }
    if hessian_full_3d:
        target_hessian_matrix = _tensor_at(hessian, target_index)
        projected_target_hessian = _project_hessian_to_eigenframe(
            target_hessian_matrix,
            target_eigenvectors,
        )
        projected_target_hessian = np.asarray(projected_target_hessian, dtype=float)
        (
            projected_hessian_eigenvalues,
            projected_hessian_eigenvectors,
        ) = np.linalg.eigh(projected_target_hessian)
        projected_trace = float(np.trace(projected_target_hessian))
        projected_determinant = float(np.linalg.det(projected_target_hessian))
        projected_lambda_abs_max = float(np.max(np.abs(projected_hessian_eigenvalues)))

        confinement_radius_ratio: float | None
        confinement_radius_length: float | None
        if (
            np.isfinite(target_lambda2)
            and np.isfinite(projected_lambda_abs_max)
            and projected_lambda_abs_max > 0.0
        ):
            confinement_radius_ratio = float(abs(target_lambda2) / projected_lambda_abs_max)
            confinement_radius_length = float(np.sqrt(confinement_radius_ratio))
        else:
            confinement_radius_ratio = None
            confinement_radius_length = None

        confinement_principal_axis_semiaxis_squared: list[float | None] = []
        confinement_principal_axis_semiaxis: list[float | None] = []
        if np.isfinite(target_lambda2):
            for hessian_eig in projected_hessian_eigenvalues:
                if target_lambda2 < 0.0 and np.isfinite(hessian_eig) and hessian_eig > 0.0:
                    semi_axis_sq = float(-target_lambda2 / hessian_eig)
                    confinement_principal_axis_semiaxis_squared.append(
                        semi_axis_sq if semi_axis_sq >= 0.0 else None
                    )
                    confinement_principal_axis_semiaxis.append(
                        float(np.sqrt(semi_axis_sq)) if semi_axis_sq >= 0.0 else None
                    )
                else:
                    confinement_principal_axis_semiaxis_squared.append(None)
                    confinement_principal_axis_semiaxis.append(None)
        else:
            confinement_principal_axis_semiaxis_squared = [None, None, None]
            confinement_principal_axis_semiaxis = [None, None, None]
        target_hessian_full_3d.update(
            {
                "hessian_full_3d_enabled": True,
                "target_hessian_full_3d_projection_matrix": _jsonify_matrix(
                    projected_target_hessian
                ),
                "target_hessian_full_3d_entry_h11": float(projected_target_hessian[0, 0]),
                "target_hessian_full_3d_entry_h22": float(projected_target_hessian[1, 1]),
                "target_hessian_full_3d_entry_h33": float(projected_target_hessian[2, 2]),
                "target_hessian_full_3d_entry_h12": float(projected_target_hessian[0, 1]),
                "target_hessian_full_3d_entry_h13": float(projected_target_hessian[0, 2]),
                "target_hessian_full_3d_entry_h23": float(projected_target_hessian[1, 2]),
                "target_hessian_full_3d_eigenvalues": _jsonify_vector(
                    projected_hessian_eigenvalues
                ),
                "target_hessian_full_3d_eigenvectors": _jsonify_matrix(
                    projected_hessian_eigenvectors
                ),
                "target_hessian_full_3d_trace": projected_trace,
                "target_hessian_full_3d_determinant": projected_determinant,
                "target_hessian_full_3d_e3e3": float(projected_target_hessian[2, 2]),
                "target_hessian_full_3d_lambda_max": projected_lambda_abs_max,
                "target_hessian_full_3d_confinement_radius_estimate": confinement_radius_ratio,
                "target_hessian_full_3d_confinement_radius_ratio": confinement_radius_ratio,
                "target_hessian_full_3d_confinement_radius_ratio_units": "length^2",
                "target_hessian_full_3d_confinement_radius_estimate_units": "length^2",
                "target_hessian_full_3d_confinement_radius_ratio_abs_lambda2_over_abs_lambda_max": (
                    confinement_radius_ratio
                ),
                "target_hessian_full_3d_confinement_radius_ratio_abs_lambda2_over_abs_lambda_max_units": "length^2",
                "target_hessian_full_3d_confinement_radius_length_abs_lambda2_over_abs_lambda_max": (
                    confinement_radius_length
                ),
                "target_hessian_full_3d_confinement_radius_length_abs_lambda2_over_abs_lambda_max_units": (
                    "length"
                ),
                "target_hessian_full_3d_confinement_radius_length": confinement_radius_length,
                "target_hessian_full_3d_confinement_radius_length_units": "length",
                "target_hessian_full_3d_taylor_principal_axis_semi_axis_squared": (
                    confinement_principal_axis_semiaxis_squared
                ),
                "target_hessian_full_3d_taylor_principal_axis_semi_axis": (
                    confinement_principal_axis_semiaxis
                ),
                "target_hessian_full_3d_taylor_principal_axis_semi_axis_units": "length",
                "target_hessian_full_3d_taylor_principal_axes_in_target_strain_eigenframe": (
                    _jsonify_matrix(projected_hessian_eigenvectors)
                ),
            }
        )

    local_hessian = _tensor_at(hessian, max_index)
    cross_derivative = _directional_hessian_cross(hessian, max_index, e1, e2)
    pressure_hessian_e1_e2 = _directional_hessian_cross(
        pressure_hessian,
        max_index,
        e1,
        e2,
    )
    hess_omega2_e1_e2 = _directional_hessian_cross(
        spectral_hessian(enstrophy, axis_convention=derivative_axis_convention),
        max_index,
        e1,
        e2,
    )
    hess_S2_e1_e2 = _directional_hessian_cross(
        spectral_hessian(strain_norm_squared, axis_convention=derivative_axis_convention),
        max_index,
        e1,
        e2,
    )
    kato_alignment_result: dict[str, Any] = {}
    strain_grad_for_kato: np.ndarray | None = None
    if kato_alignment or kato_stability_statistics:
        strain_grad_for_kato = strain_gradient_tensor(
            strain,
            axis_convention=derivative_axis_convention,
        )
    if kato_alignment:
        if strain_grad_for_kato is None:
            raise RuntimeError("internal error: missing strain gradient for Kato alignment")
        d_e1S_e1 = _directional_strain_gradient_vector(
            strain_grad_for_kato,
            target_index,
            target_e1,
            target_e1,
        )
        d_e2S_e1 = _directional_strain_gradient_vector(
            strain_grad_for_kato,
            target_index,
            target_e2,
            target_e1,
        )
        if not np.all(np.isfinite(d_e1S_e1)) or not np.all(np.isfinite(d_e2S_e1)):
            raise ValueError("Kato alignment directional projected vectors contain non-finite values")
        e2_d_e1S_e1 = _directional_strain_gradient_projection(
            strain_grad_for_kato,
            target_index,
            target_e2,
            target_e1,
            target_e1,
        )
        e2_d_e2S_e1 = _directional_strain_gradient_projection(
            strain_grad_for_kato,
            target_index,
            target_e2,
            target_e1,
            target_e2,
        )
        if not np.isfinite(e2_d_e1S_e1) or not np.isfinite(e2_d_e2S_e1):
            raise ValueError("Kato alignment directional projections are non-finite")
        kato_alignment_B = 2.0 * e2_d_e1S_e1 * e2_d_e2S_e1
        if not np.isfinite(kato_alignment_B):
            raise ValueError("Kato alignment condition B is non-finite")
        kato_alignment_result = {
            "kato_alignment_enabled": True,
            "kato_alignment_computed": True,
            "kato_alignment_target_snapshot_available": True,
            "kato_alignment_directional_grad_e1_vector": _jsonify_vector(d_e1S_e1),
            "kato_alignment_directional_grad_e2_vector": _jsonify_vector(d_e2S_e1),
            "kato_alignment_e2_dot_d_e1S_e1": e2_d_e1S_e1,
            "kato_alignment_e2_dot_d_e2S_e1": e2_d_e2S_e1,
            "kato_alignment_B": float(kato_alignment_B),
            "kato_alignment_target_index": list(target_index),
            "kato_alignment_target_mode": target,
            "kato_alignment_lambda2_at_target": float(target_lambda2),
            "kato_alignment_target_lambda2": float(target_lambda2),
            "kato_alignment_target_pressure_hessian_e1_e2": float(target_pressure_hessian_e1_e2),
            "kato_alignment_target_cross_derivative_e1_e2_lambda2": float(target_cross_derivative),
            "kato_alignment_cross_derivative_e1_e2_lambda2_at_target": float(target_cross_derivative),
            "kato_alignment_pressure_hessian_e1_e2_at_target": float(target_pressure_hessian_e1_e2),
        }
        kato_alignment_result["kato_alignment_B_sign"] = classify_sign(
            kato_alignment_result["kato_alignment_B"]
        )
        if not np.isfinite(kato_alignment_result["kato_alignment_B"]):
            raise ValueError("Kato alignment condition B is non-finite")
    pressure_hessian_local_decomposition_tail = (
        pressure_hessian_e1_e2
        - (-0.5 * hess_omega2_e1_e2 + hess_S2_e1_e2)
    )
    vorticity_dominance_margin = (
        0.5 * abs(hess_omega2_e1_e2)
        - (abs(hess_S2_e1_e2) + abs(pressure_hessian_local_decomposition_tail))
    )
    vorticity_dominance_condition_holds = bool(vorticity_dominance_margin > 0.0)
    sign_classification = classify_sign(cross_derivative)
    diagnostic_status, sign_evidence_for_promotion, sign_evidence_blocker = _diagnostic_status(
        source=source,
        field_metadata=field_metadata,
        eigenframe_degenerate=eigenframe_degenerate,
        sign_classification=sign_classification,
    )

    max_vorticity = omega[(slice(None),) + max_index]
    output_path = Path(output) if output is not None else None
    result: dict[str, Any] = {
        "diagnostic": "NS-GW-1 strain cross-derivative",
        "result_format": JSON_FORMAT,
        "result_artifact_path": str(output_path) if output_path is not None else None,
        "result_artifact_format": "json" if output_path is not None else "stdout_json",
        "diagnostic_scope": (
            "single periodic-grid numerical probe for the nonlinear Riesz sign "
            "route; reports the legacy enstrophy-maximum snapshot and the selected "
            "target-point snapshot"
        ),
        "grid_N": n,
        "grid_spacing": grid_spacing,
        "domain_length": float(DOMAIN_LENGTH),
        "domain": "[0, 2*pi)^3 periodic",
        "source": source,
        "field_metadata": field_metadata,
        "amplitude": float(amplitude),
        "target_mode": target,
        "target_selection_status": target_selection["target_selection_status"],
        "target_selection_blocker": target_selection["target_selection_blocker"],
        "target_top_enstrophy_percentile": float(target_selection["target_top_enstrophy_percentile"]),
        "target_top_enstrophy_threshold": target_selection.get("target_top_enstrophy_threshold"),
        "target_top_enstrophy_mask_count": target_selection.get("target_top_enstrophy_mask_count"),
        "target_negative_lambda2_top_mask_count": target_selection.get("target_negative_lambda2_top_mask_count"),
        **_target_snapshot_payload(
            target_index=target_index,
            target_enstrophy=float(enstrophy[target_index]),
            target_strain_norm_squared=float(strain_norm_squared[target_index]),
            target_eigenvalues=target_eigenvalues,
            target_eigenvectors=target_eigenvectors,
            target_min_local_eigenvalue_gap=target_min_eigenvalue_gap,
            target_eigenframe_degenerate=target_eigenframe_degenerate,
            target_lambda2=target_lambda2,
            target_cross_derivative=target_cross_derivative,
            target_pressure_hessian_e1_e2=target_pressure_hessian_e1_e2,
        ),
        **target_hessian_full_3d,
        "target_sign_classification": target_sign_classification,
        "target_sign_nonpositive": bool(
            target_sign_classification != "positive_adverse_to_nonpositive_rule"
        ),
        "target_diagnostic_status": target_diagnostic_status,
        "target_sign_evidence_for_promotion": target_sign_evidence_for_promotion,
        "target_sign_evidence_blocker": target_sign_evidence_blocker,
        "enstrophy_max_index": list(max_index),
        "enstrophy_max_value": float(enstrophy[max_index]),
        "vorticity_at_max": _jsonify_vector(max_vorticity),
        "eigenvalues_at_max": _jsonify_vector(local_eigenvalues),
        "eigenvectors_at_max": _jsonify_matrix(local_eigenvectors),
        "eigenvector_convention": (
            "columns are numpy.linalg.eigh eigenvectors ordered by ascending "
            "strain eigenvalue; e1 is most compressive and e2 is intermediate"
        ),
        "min_local_eigenvalue_gap": min_eigenvalue_gap,
        "eigenframe_degenerate": eigenframe_degenerate,
        "lambda2_at_max": lambda2,
        "lambda2_gradient_at_max": _jsonify_vector(lambda2_gradient[(slice(None),) + max_index]),
        "lambda2_hessian_at_max": _jsonify_matrix(local_hessian),
        "cross_derivative_e1_e2_lambda2_at_max": cross_derivative,
        "pressure_hessian_e1_e2_at_max": pressure_hessian_e1_e2,
        "hess_omega2_e1_e2_at_max": hess_omega2_e1_e2,
        "hess_S2_e1_e2_at_max": hess_S2_e1_e2,
        "cross_derivative_e1_e2_pressure_at_max": pressure_hessian_e1_e2,
        "cross_derivative_e1_e2_vorticity_norm_squared_at_max": hess_omega2_e1_e2,
        "cross_derivative_e1_e2_strain_norm_squared_at_max": hess_S2_e1_e2,
        "pressure_hessian_local_decomposition_tail_e1_e2_at_max": (
            pressure_hessian_local_decomposition_tail
        ),
        "vorticity_dominance_margin": vorticity_dominance_margin,
        "vorticity_dominance_rule": (
            "abs(hess_S2_e1_e2 + tail bound split as abs(hess_S2_e1_e2) "
            "+ abs(pressure_hessian_local_decomposition_tail_e1_e2)) "
            "< 0.5 * abs(hess_omega2_e1_e2)"
        ),
        "vorticity_dominance_condition_holds": vorticity_dominance_condition_holds,
        "pressure_poisson_equation": "-Delta p = |S|^2 - 0.5*|omega|^2",
        "pressure_poisson_identity_assumption": "incompressible_periodic_velocity",
        "pressure_poisson_rhs_at_max": float(pressure_poisson_rhs[max_index]),
        "pressure_poisson_rhs_mean": float(np.mean(pressure_poisson_rhs)),
        "strain_norm_squared_at_max": float(strain_norm_squared[max_index]),
        "half_vorticity_norm_squared_at_max": 0.5 * float(enstrophy[max_index]),
        "derivative_operator_axis_convention": derivative_axis_convention,
        "target_derivative_operator_axis_convention": derivative_axis_convention,
        "divergence_max_abs": float(np.max(np.abs(divergence))),
        "divergence_l2_mean": float(np.sqrt(np.mean(divergence * divergence))),
        "divergence_max_abs_xyz_storage": float(np.max(np.abs(divergence_xyz_storage))),
        "divergence_l2_mean_xyz_storage": float(
            np.sqrt(np.mean(divergence_xyz_storage * divergence_xyz_storage))
        ),
        "divergence_max_abs_zyx_storage": float(np.max(np.abs(divergence_zyx_storage))),
        "divergence_l2_mean_zyx_storage": float(
            np.sqrt(np.mean(divergence_zyx_storage * divergence_zyx_storage))
        ),
        "sign_nonpositive_at_max": bool(
            sign_classification != "positive_adverse_to_nonpositive_rule"
        ),
        "sign_classification": sign_classification,
        "sign_tolerance": float(SIGN_TOLERANCE),
        "sign_rule": "cross_derivative_d_e1_d_e2_lambda2 <= 0",
        "diagnostic_status": diagnostic_status,
        "sign_evidence_for_promotion": sign_evidence_for_promotion,
        "sign_evidence_blocker": sign_evidence_blocker,
        "dns_time_window_required": DNS_TIME_WINDOW_REQUIRED,
        "degeneracy_conclusion": (
            "nine-result conclusion: t=0 synthetic/fixture eigenframe_degenerate=true; "
            "zero/noise cross derivative is not evidence for sign; real DNS t≈7-9 required"
        ),
        "promotion_allowed": False,
        "nonlinear_riesz_sign_condition_confirmed": False,
        "caveat": CAVEAT,
    }
    result.update(kato_alignment_result)
    if kato_stability_statistics:
        if strain_grad_for_kato is None:
            raise RuntimeError("internal error: missing strain gradient for Kato statistics")
        result.update(
            _kato_stability_statistics(
                strain=strain,
                strain_gradient=strain_grad_for_kato,
                lambda2_field=lambda2_field,
                lambda2_hessian=hessian,
                lambda2_min=lambda2_min,
                kato_beta_threshold=kato_beta_threshold,
            )
        )
    if integral_conditions:
        cell_volume = float(grid_spacing ** 3)
        pressure_hessian_e1_e2_field = np.einsum(
            "i,ijxyz,j->xyz",
            target_e1,
            pressure_hessian,
            target_e2,
        )
        condition_weights: list[tuple[str, np.ndarray, dict[str, Any]]] = [
            (
                "lambda2_negative_mask",
                (lambda2_field < 0.0).astype(float),
                {"support_type": "lambda2<0"},
            ),
            (
                "omega2_weight",
                enstrophy,
                {"support_type": "omega2"},
            ),
            (
                "S2_weight",
                strain_norm_squared,
                {"support_type": "S2"},
            ),
        ]
        if top_enstrophy_percentile is not None:
            enstrophy_threshold = float(np.percentile(enstrophy, top_enstrophy_percentile))
            condition_weights.append(
                (
                    "top_enstrophy_percentile",
                    (enstrophy >= enstrophy_threshold).astype(float),
                    {
                        "support_type": "top_enstrophy_mask",
                        "percentile": float(top_enstrophy_percentile),
                        "threshold": enstrophy_threshold,
                    },
                )
            )
        integral_condition_fields: dict[str, dict[str, Any]] = {}
        for field_name, field_values in (
            ("Qcrit_pressure_hessian_e1_e2", pressure_hessian_e1_e2_field),
            ("pressure_poisson_rhs", pressure_poisson_rhs),
        ):
            field_summary: dict[str, Any] = {}
            for weight_name, weight_values, weight_metadata in condition_weights:
                stats = _weighted_field_statistics(field_values, weight_values, cell_volume)
                field_summary[weight_name] = {
                    **weight_metadata,
                    **stats,
                }
            integral_condition_fields[field_name] = field_summary
        result["integral_conditions_enabled"] = True
        result["integral_conditions_target_mode"] = target
        result["integral_conditions_target_index"] = list(target_index)
        if top_enstrophy_percentile is not None:
            result["integral_conditions_top_enstrophy_percentile"] = float(top_enstrophy_percentile)
            result["integral_conditions_top_enstrophy_threshold"] = float(enstrophy_threshold)
        result["integral_conditions"] = {
            "cell_volume": cell_volume,
            "reference_target_mode": target,
            "reference_target_index": list(target_index),
            "weight_fields": [name for name, _, _ in condition_weights],
            "fields": integral_condition_fields,
        }
    result["summary"] = format_summary(result)
    if output_path is not None:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  scripts/ns_gateway1_strain_cross_derivative_diagnostic.py --N 16\n"
            "  scripts/ns_gateway1_fixture_npz.py --N 16 --amplitude 0.75 "
            "--output /tmp/ns_gw1_fixture.npz\n"
            "  scripts/ns_gateway1_strain_cross_derivative_diagnostic.py "
            "--field /tmp/ns_gw1_fixture.npz --output /tmp/ns_gw1_result.json\n"
            "  scripts/ns_gateway1_strain_cross_derivative_diagnostic.py "
            "--integral-conditions --top-enstrophy-percentile 95 --output /tmp/ns_gw1_result.json\n"
            "  scripts/ns_gateway1_strain_cross_derivative_diagnostic.py "
            "--kato-alignment --output /tmp/ns_gw1_result.json\n\n"
            "  scripts/ns_gateway1_strain_cross_derivative_diagnostic.py "
            "--target lambda2_negative_top_enstrophy --target-top-enstrophy-percentile 90 "
            "--output /tmp/ns_gw1_result.json\n\n"
            "Input NPZ contract: cubic real arrays named u, v, w on [0, 2*pi)^3; "
            "optional scalar metadata N, domain_length, grid_spacing, amplitude, "
            "time, snapshot_index, and source are validated/reported."
        ),
    )
    parser.add_argument(
        "--N",
        type=int,
        default=32,
        help="cubic grid size for the synthetic Taylor-Green field; ignored when --field is supplied",
    )
    parser.add_argument(
        "--amplitude",
        type=float,
        default=1.0,
        help="synthetic Taylor-Green amplitude; ignored when --field is supplied",
    )
    parser.add_argument("--field", type=Path, default=None, help="optional NPZ containing 3D arrays u, v, w")
    parser.add_argument("--output", type=Path, default=None, help="optional JSON artifact output path")
    parser.add_argument(
        "--target",
        choices=TARGET_MODES,
        default="enstrophy_max",
        help="select the target point used for target-dependent diagnostics",
    )
    parser.add_argument(
        "--target-top-enstrophy-percentile",
        type=float,
        default=90.0,
        help="top-enstrophy percentile used by --target lambda2_negative_top_enstrophy",
    )
    parser.add_argument(
        "--integral-conditions",
        action="store_true",
        help=(
            "report weighted integral/average diagnostics over lambda2<0, omega2, S2, "
            "and optional top-enstrophy support"
        ),
    )
    parser.add_argument(
        "--top-enstrophy-percentile",
        type=float,
        default=None,
        help="optional top-enstrophy percentile threshold for the integral-condition mode",
    )
    parser.add_argument(
        "--kato-alignment",
        action="store_true",
        help="compute and report Kato strain-gradient alignment condition B at the target point",
    )
    parser.add_argument(
        "--kato-stability-statistics",
        action="store_true",
        help="compute aggregate Kato mixed-plane stability statistics over the lambda2<0 region",
    )
    parser.add_argument(
        "--kato-beta-threshold",
        type=float,
        default=None,
        help=(
            "optional threshold ratio theta in (0, 1) for bounded Omega_beta "
            "metrics where beta = theta * lambda2_min"
        ),
    )
    parser.add_argument(
        "--hessian-full-3d",
        action="store_true",
        help=(
            "compute and report the full Hessian(lambda2) at the selected target in "
            "its local strain eigenframe (h11,h22,h33,h12,h13,h23), eigenvalues, "
            "trace, determinant, e3e3, lambda_max, and confinement geometry metrics"
        ),
    )
    parser.add_argument("--json-indent", type=int, default=2, help="JSON indentation level for stdout JSON")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    result = run_diagnostic(
        N=args.N,
        amplitude=args.amplitude,
        field=args.field,
        output=args.output,
        target=args.target,
        target_top_enstrophy_percentile=args.target_top_enstrophy_percentile,
        integral_conditions=args.integral_conditions,
        top_enstrophy_percentile=args.top_enstrophy_percentile,
        kato_alignment=args.kato_alignment,
        kato_stability_statistics=args.kato_stability_statistics,
        kato_beta_threshold=args.kato_beta_threshold,
        hessian_full_3d=args.hessian_full_3d,
    )
    if args.output is None:
        print(json.dumps(result, indent=args.json_indent, sort_keys=True))
    else:
        print(result["summary"])


if __name__ == "__main__":
    main()
