#!/usr/bin/env python3
"""NS-GW-1 strain cross-derivative numerical diagnostic.

This script is an evidence-only numerical diagnostic for periodic 3D velocity
fields on ``[0, 2*pi)^3``.  It computes the strain eigenframe at the maximum
vorticity point and measures the local directional cross derivative
``d_{e1} d_{e2} lambda2`` of the intermediate strain eigenvalue field.

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
    index = tuple(result["enstrophy_max_index"])
    cross = float(result["cross_derivative_e1_e2_lambda2_at_max"])
    classification = str(result["sign_classification"])
    status = str(result["diagnostic_status"])
    artifact = result.get("result_artifact_path")
    artifact_text = f", artifact={artifact}" if artifact else ""
    return (
        "NS-GW-1 diagnostic: "
        f"source={source}, N={int(result['grid_N'])}, "
        f"enstrophy_max_index={index}, "
        f"d_e1_d_e2_lambda2={cross:.17g}, "
        f"classification={classification}, "
        f"status={status}{artifact_text}"
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
) -> dict[str, Any]:
    """Run the NS-GW-1 diagnostic and return a JSON-serializable dict.

    ``field`` is an optional ``.npz`` path containing cubic 3D arrays named
    ``u``, ``v``, and ``w`` sampled on ``[0, 2*pi)^3``.  ``N`` and
    ``amplitude`` control only the deterministic built-in Taylor-Green field.
    """

    if int(N) != N:
        raise ValueError(f"N must be an integer, got {N!r}")
    N = int(N)
    amplitude = float(amplitude)
    if not np.isfinite(amplitude):
        raise ValueError("amplitude must be finite")

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
    local_hessian = _tensor_at(hessian, max_index)
    cross_derivative = _directional_hessian_cross(hessian, max_index, e1, e2)
    pressure_hessian_e1_e2 = _directional_hessian_cross(
        spectral_hessian(pressure, axis_convention=derivative_axis_convention),
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
            "route; reports only the enstrophy-maximum local value"
        ),
        "grid_N": n,
        "grid_spacing": grid_spacing,
        "domain_length": float(DOMAIN_LENGTH),
        "domain": "[0, 2*pi)^3 periodic",
        "source": source,
        "field_metadata": field_metadata,
        "amplitude": float(amplitude),
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
            "--field /tmp/ns_gw1_fixture.npz --output /tmp/ns_gw1_result.json\n\n"
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
    parser.add_argument("--json-indent", type=int, default=2, help="JSON indentation level for stdout JSON")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    result = run_diagnostic(N=args.N, amplitude=args.amplitude, field=args.field, output=args.output)
    if args.output is None:
        print(json.dumps(result, indent=args.json_indent, sort_keys=True))
    else:
        print(result["summary"])


if __name__ == "__main__":
    main()
