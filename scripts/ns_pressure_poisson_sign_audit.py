#!/usr/bin/env python3
"""Audit pressure-Poisson sign/convention mismatches on NS archives.

The script consumes a raw pressure NPZ or a derived NS archive, extracts one
frame, computes a spectral ``Delta p`` and ``-Delta p``, and compares those
against the pressure-Poisson source proxy
``tr(S^2) - |omega|^2 / 4`` when the needed velocity or tensor fields are
available.

The output is deterministic JSON and is fail-closed: it records the best sign
proxy, the comparison table, and explanation notes, but never claims theorem or
promotion authority.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_pressure_poisson_sign_audit.py"
DEFAULT_OUTPUT = Path("outputs/ns_pressure_poisson_sign_audit.json")
OK_STATUS = "ok"
STATUS_MISSING_REQUIRED_FIELD = "missing_required_field"
STATUS_NO_PROXY = "proxy_unavailable"

PRESSURE_KEYS = (
    "pressure_snapshots",
    "pressure",
    "p",
    "pressure_hat",
    "p_hat",
)

STRAIN_SQ_KEYS = (
    "strain_norm_squared",
    "strain_sq",
    "strain_frobenius_sq",
    "S2",
    "tr_S2",
    "trS2",
)

OMEGA_SQ_KEYS = (
    "omega_norm_sq",
    "omega_sq",
    "vorticity_norm_sq",
    "enstrophy",
    "omega2",
)

VELOCITY_COMPONENT_SETS = (
    ("u", "v", "w"),
    ("u_snapshots", "v_snapshots", "w_snapshots"),
    ("u_hat", "v_hat", "w_hat"),
    ("velocity_x", "velocity_y", "velocity_z"),
    ("v_x", "v_y", "v_z"),
)

OMEGA_COMPONENT_SETS = (
    ("omega_x", "omega_y", "omega_z"),
    ("omega1", "omega2", "omega3"),
    ("vorticity_x", "vorticity_y", "vorticity_z"),
)

CONTROL_CARD = {
    "O": "Audit a pressure sign and convention mismatch on one NS frame.",
    "R": "Compare spectral Delta p and -Delta p against tr(S^2) - |omega|^2 / 4 when the proxy fields are available.",
    "C": "One stdlib Python script writes deterministic JSON only.",
    "S": "The audit is fail-closed and records comparison evidence without any theorem or promotion claim.",
    "L": "pressure -> spectral Laplacian -> source proxy -> sign/scale comparison -> violation notes.",
    "P": "Use the best-fitting sign and scale to localize the convention drift behind the bypass violation.",
    "G": "Authority stays false and no Clay or theorem promotion is allowed.",
    "F": "Missing pressure or proxy fields block a definitive sign audit.",
}


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return float(parsed)


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be a nonnegative integer")
    return parsed


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {name: np.asarray(data[name]) for name in data.files}


def _scalar_metadata(data: dict[str, np.ndarray], *names: str) -> tuple[Any | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape != ():
            continue
        scalar = value.item()
        if isinstance(scalar, bytes):
            scalar = scalar.decode("utf-8")
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        return scalar, name
    return None, None


def _select_frame(value: np.ndarray, frame: int | None, name: str) -> np.ndarray:
    arr = np.asarray(value)
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
    arr = np.asarray(arr, dtype=np.float64)
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} contains non-finite values")
    return arr


def _select_vector_frame(value: np.ndarray, frame: int | None, name: str) -> np.ndarray:
    arr = np.asarray(value)
    if arr.ndim == 4:
        if arr.shape[0] == 3:
            arr = arr
        elif arr.shape[-1] == 3:
            arr = np.moveaxis(arr, -1, 0)
        else:
            raise ValueError(f"{name} must store 3 components along axis 0 or -1, got {arr.shape!r}")
    elif arr.ndim == 5:
        if arr.shape[1] == 3:
            arr = arr
        elif arr.shape[-1] == 3:
            arr = np.moveaxis(arr, -1, 1)
        else:
            raise ValueError(f"{name} must store 3 components along axis 1 or -1, got {arr.shape!r}")
        if frame is None:
            if int(arr.shape[0]) != 1:
                raise ValueError(f"{name} has {arr.shape[0]} frame(s); pass --frame")
            arr = arr[0]
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frame(s)")
            arr = arr[frame]
        if arr.shape[0] != 3:
            raise ValueError(f"{name} does not expose 3 velocity/vorticity components")
        arr = np.asarray(arr, dtype=np.float64)
        if not np.all(np.isfinite(arr)):
            raise ValueError(f"{name} contains non-finite values")
        return arr
    else:
        raise ValueError(f"{name} must be 4D or 5D stacked vector data, got {arr.shape!r}")

    if frame is not None:
        raise ValueError(f"{name} does not carry a frame axis; omit --frame for this field")
    arr = np.asarray(arr, dtype=np.float64)
    if arr.shape[0] != 3:
        raise ValueError(f"{name} does not expose 3 vector components")
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} contains non-finite values")
    return arr


def _spatial_axes(arr: np.ndarray) -> tuple[int, int, int]:
    if arr.ndim != 3:
        raise ValueError(f"expected a 3D scalar field, got {arr.shape!r}")
    return (0, 1, 2)


def _frequency_grid(n: int, domain_length: float, axis: int) -> np.ndarray:
    freq = 2.0 * np.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    shape = [1, 1, 1]
    shape[axis] = n
    return freq.reshape(shape)


def _spectral_derivative(field: np.ndarray, axis: int, domain_length: float) -> np.ndarray:
    scalar = np.asarray(field, dtype=np.float64)
    if scalar.ndim != 3:
        raise ValueError(f"field must be 3D, got {scalar.shape!r}")
    n = int(scalar.shape[0])
    if scalar.shape[1] != n or scalar.shape[2] != n:
        raise ValueError(f"field must be cubic in space, got {scalar.shape!r}")
    k = _frequency_grid(n, domain_length, axis)
    transformed = np.fft.fftn(scalar, axes=_spatial_axes(scalar))
    return np.fft.ifftn(1j * k * transformed, axes=_spatial_axes(scalar)).real


def _spectral_laplacian(field: np.ndarray, domain_length: float) -> np.ndarray:
    scalar = np.asarray(field, dtype=np.float64)
    if scalar.ndim != 3:
        raise ValueError(f"field must be 3D, got {scalar.shape!r}")
    n = int(scalar.shape[0])
    if scalar.shape[1] != n or scalar.shape[2] != n:
        raise ValueError(f"field must be cubic in space, got {scalar.shape!r}")
    kx = _frequency_grid(n, domain_length, 0)
    ky = _frequency_grid(n, domain_length, 1)
    kz = _frequency_grid(n, domain_length, 2)
    k2 = kx * kx + ky * ky + kz * kz
    transformed = np.fft.fftn(scalar, axes=_spatial_axes(scalar))
    return np.fft.ifftn(-k2 * transformed, axes=_spatial_axes(scalar)).real


def _velocity_gradient(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    if u.shape != v.shape or u.shape != w.shape:
        raise ValueError(f"velocity component shapes differ: {u.shape!r}, {v.shape!r}, {w.shape!r}")
    grad = np.empty((3, 3) + u.shape, dtype=np.float64)
    for component_index, component in enumerate((u, v, w)):
        for axis in range(3):
            grad[component_index, axis] = _spectral_derivative(component, axis, domain_length)
    return grad


def _strain_tensor(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    if tensor.ndim != 5 or tensor.shape[:2] != (3, 3):
        raise ValueError(f"grad must have shape (3,3,N,N,N), got {tensor.shape!r}")
    return 0.5 * (tensor + np.swapaxes(tensor, 0, 1))


def _vorticity_from_gradient(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    if tensor.ndim != 5 or tensor.shape[:2] != (3, 3):
        raise ValueError(f"grad must have shape (3,3,N,N,N), got {tensor.shape!r}")
    omega = np.empty((3,) + tensor.shape[2:], dtype=np.float64)
    omega[0] = tensor[2, 1] - tensor[1, 2]
    omega[1] = tensor[0, 2] - tensor[2, 0]
    omega[2] = tensor[1, 0] - tensor[0, 1]
    return omega


def _tensor_frobenius_squared(tensor: np.ndarray) -> np.ndarray:
    arr = np.asarray(tensor, dtype=np.float64)
    if arr.ndim != 5 or arr.shape[:2] != (3, 3):
        raise ValueError(f"tensor must have shape (3,3,N,N,N), got {arr.shape!r}")
    return np.sum(arr * arr, axis=(0, 1))


def _vector_norm_squared(vector: np.ndarray) -> np.ndarray:
    arr = np.asarray(vector, dtype=np.float64)
    if arr.ndim != 4 or arr.shape[0] != 3:
        raise ValueError(f"vector must have shape (3,N,N,N), got {arr.shape!r}")
    return np.sum(arr * arr, axis=0)


def _pearson_correlation(a: np.ndarray, b: np.ndarray) -> float | None:
    a_flat = np.asarray(a, dtype=np.float64).ravel()
    b_flat = np.asarray(b, dtype=np.float64).ravel()
    mask = np.isfinite(a_flat) & np.isfinite(b_flat)
    a_sel = a_flat[mask]
    b_sel = b_flat[mask]
    if a_sel.size < 2:
        return None
    a_centered = a_sel - float(np.mean(a_sel))
    b_centered = b_sel - float(np.mean(b_sel))
    a_scale = float(np.linalg.norm(a_centered))
    b_scale = float(np.linalg.norm(b_centered))
    if a_scale == 0.0 or b_scale == 0.0:
        return None
    return float(np.dot(a_centered, b_centered) / (a_scale * b_scale))


def _rmse(a: np.ndarray, b: np.ndarray) -> float:
    diff = np.asarray(a, dtype=np.float64) - np.asarray(b, dtype=np.float64)
    return float(np.sqrt(np.mean(diff * diff)))


def _positive_best_scale(reference: np.ndarray, candidate: np.ndarray) -> float:
    ref = np.asarray(reference, dtype=np.float64).ravel()
    cand = np.asarray(candidate, dtype=np.float64).ravel()
    mask = np.isfinite(ref) & np.isfinite(cand)
    ref = ref[mask]
    cand = cand[mask]
    denom = float(np.dot(cand, cand))
    if denom <= 0.0:
        return 0.0
    scale = float(np.dot(ref, cand) / denom)
    return 0.0 if scale <= 0.0 else scale


def _load_pressure_field(data: dict[str, np.ndarray], frame: int | None) -> tuple[np.ndarray | None, str | None]:
    for key in PRESSURE_KEYS:
        if key not in data:
            continue
        arr = np.asarray(data[key])
        if np.iscomplexobj(arr):
            if arr.ndim == 4:
                if frame is None:
                    if int(arr.shape[0]) != 1:
                        raise ValueError(f"{key} has {arr.shape[0]} frame(s); pass --frame")
                    arr = arr[0]
                else:
                    if frame < 0 or frame >= int(arr.shape[0]):
                        raise ValueError(f"{key} frame {frame} is out of range for {arr.shape[0]} frame(s)")
                    arr = arr[frame]
            if arr.ndim != 3:
                raise ValueError(f"{key} must be 3D or single-snapshot 4D, got {arr.shape!r}")
            pressure = np.fft.ifftn(arr, axes=(0, 1, 2)).real
            if not np.all(np.isfinite(pressure)):
                raise ValueError(f"{key} contains non-finite values")
            return np.asarray(pressure, dtype=np.float64), key
        return _select_frame(arr, frame, key), key
    return None, None


def _load_scalar_field(data: dict[str, np.ndarray], keys: tuple[str, ...], frame: int | None) -> tuple[np.ndarray | None, str | None]:
    for key in keys:
        if key not in data:
            continue
        try:
            return _select_frame(data[key], frame, key), key
        except ValueError:
            continue
    return None, None


def _load_vector_components(
    data: dict[str, np.ndarray],
    frame: int | None,
    keysets: tuple[tuple[str, str, str], ...],
) -> tuple[tuple[np.ndarray, np.ndarray, np.ndarray] | None, str | None]:
    for keyset in keysets:
        if all(key in data for key in keyset):
            components = [_select_frame(data[key], frame, key) for key in keyset]
            shapes = {component.shape for component in components}
            if len(shapes) != 1:
                raise ValueError(f"vector component shapes differ for {keyset!r}: {sorted(shapes)!r}")
            return (components[0], components[1], components[2]), "+".join(keyset)

    for key in ("velocity", "velocity_snapshots"):
        if key not in data:
            continue
        arr = _select_vector_frame(data[key], frame, key)
        return (arr[0], arr[1], arr[2]), key

    return None, None


def _resolve_domain_length(data: dict[str, np.ndarray], n: int, override: float | None) -> tuple[float, str]:
    if override is not None:
        domain_length = _finite_float(override, "--domain-length")
        if domain_length <= 0.0:
            raise ValueError("--domain-length must be positive")
        for name in ("domain_length", "length"):
            declared, declared_name = _scalar_metadata(data, name)
            if declared is None:
                continue
            declared_float = _finite_float(declared, str(declared_name))
            if not math.isclose(declared_float, domain_length, rel_tol=1.0e-12, abs_tol=1.0e-12):
                raise ValueError(
                    f"{declared_name} metadata {declared_float:.17g} does not match --domain-length {domain_length:.17g}"
                )
        spacing_value, spacing_name = _scalar_metadata(data, "grid_spacing")
        if spacing_value is not None:
            spacing_float = _finite_float(spacing_value, str(spacing_name))
            expected = domain_length / float(n)
            if not math.isclose(spacing_float, expected, rel_tol=1.0e-12, abs_tol=1.0e-12):
                raise ValueError(
                    f"{spacing_name} metadata {spacing_float:.17g} does not match domain_length/N {expected:.17g}"
                )
        return domain_length, "cli"

    domain_value, domain_name = _scalar_metadata(data, "domain_length", "length")
    spacing_value, spacing_name = _scalar_metadata(data, "grid_spacing")
    if domain_value is not None:
        domain_length = _finite_float(domain_value, str(domain_name))
        if domain_length <= 0.0:
            raise ValueError(f"{domain_name} must be positive")
        if spacing_value is not None:
            spacing_float = _finite_float(spacing_value, str(spacing_name))
            if spacing_float <= 0.0:
                raise ValueError(f"{spacing_name} must be positive")
            expected = domain_length / float(n)
            if not math.isclose(spacing_float, expected, rel_tol=1.0e-12, abs_tol=1.0e-12):
                raise ValueError(
                    f"{spacing_name} metadata {spacing_float:.17g} does not match domain_length/N {expected:.17g}"
                )
        return domain_length, str(domain_name)

    if spacing_value is not None:
        spacing_float = _finite_float(spacing_value, str(spacing_name))
        if spacing_float <= 0.0:
            raise ValueError(f"{spacing_name} must be positive")
        return spacing_float * float(n), str(spacing_name)

    return float(n), "index_units"


def _best_sign_proxy(source_proxy: np.ndarray, laplacian: np.ndarray) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    comparisons: list[dict[str, Any]] = []
    candidate_specs = (
        ("minus", -1.0, "-Delta p"),
        ("plus", 1.0, "+Delta p"),
    )
    for sign_name, sign_factor, label in candidate_specs:
        signed_laplacian = sign_factor * np.asarray(laplacian, dtype=np.float64)
        raw_rmse = _rmse(source_proxy, signed_laplacian)
        raw_correlation = _pearson_correlation(source_proxy, signed_laplacian)
        scale = _positive_best_scale(source_proxy, signed_laplacian)
        scaled = scale * signed_laplacian
        scaled_rmse = _rmse(source_proxy, scaled)
        scaled_correlation = _pearson_correlation(source_proxy, scaled)
        comparisons.append(
            {
                "candidate": label,
                "sign": sign_name,
                "sign_factor": sign_factor,
                "raw_rmse": raw_rmse,
                "raw_correlation": raw_correlation,
                "best_scale": scale,
                "scaled_rmse": scaled_rmse,
                "scaled_correlation": scaled_correlation,
            }
        )

    def ranking_key(item: dict[str, Any]) -> tuple[float, float, int]:
        corr = item["scaled_correlation"]
        corr_score = -abs(float(corr)) if corr is not None else 0.0
        sign_rank = 0 if item["sign"] == "minus" else 1
        return (float(item["scaled_rmse"]), corr_score, sign_rank)

    best = min(comparisons, key=ranking_key)
    opponent = next(entry for entry in comparisons if entry is not best)

    best_payload = {
        "candidate": best["candidate"],
        "sign": best["sign"],
        "sign_factor": best["sign_factor"],
        "raw_rmse": best["raw_rmse"],
        "raw_correlation": best["raw_correlation"],
        "best_scale": best["best_scale"],
        "scaled_rmse": best["scaled_rmse"],
        "scaled_correlation": best["scaled_correlation"],
        "opponent": {
            "candidate": opponent["candidate"],
            "sign": opponent["sign"],
            "raw_rmse": opponent["raw_rmse"],
            "scaled_rmse": opponent["scaled_rmse"],
        },
    }

    violation_kind = "no_sign_mismatch"
    if best["sign"] == "plus":
        violation_kind = "sign_convention_mismatch"
    elif best["scaled_rmse"] > 0.0 and opponent["scaled_rmse"] / best["scaled_rmse"] < 1.05:
        violation_kind = "ambiguous_sign_convention"

    violation = {
        "present": violation_kind != "no_sign_mismatch",
        "kind": violation_kind,
        "expected_sign": "-Delta p",
        "best_sign": best["candidate"],
        "notes": [],
    }
    if violation_kind == "sign_convention_mismatch":
        violation["notes"].append(
            "The best-fitting sign is +Delta p, so the source proxy aligns with the opposite convention to the canonical pressure Poisson form."
        )
    elif violation_kind == "ambiguous_sign_convention":
        violation["notes"].append(
            "The two sign conventions fit similarly after positive rescaling, so the mismatch is weakly identified."
        )
    else:
        violation["notes"].append(
            "The best-fitting sign is -Delta p, which matches the canonical pressure Poisson convention."
        )

    return best_payload, comparisons, violation


def _build_payload(args: argparse.Namespace) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "input": str(args.input),
        "frame": args.frame,
        "output_json": str(args.output_json),
        "pretty": bool(args.pretty),
        "requested_domain_length": args.domain_length,
        "authority": False,
        "status": STATUS_MISSING_REQUIRED_FIELD,
        "errors": [],
        "warnings": [],
        "O": CONTROL_CARD["O"],
        "R": CONTROL_CARD["R"],
        "C": CONTROL_CARD["C"],
        "S": CONTROL_CARD["S"],
        "L": CONTROL_CARD["L"],
        "P": CONTROL_CARD["P"],
        "G": CONTROL_CARD["G"],
        "F": CONTROL_CARD["F"],
        "best_sign_proxy": None,
        "comparisons": [],
        "violation": {
            "present": False,
            "kind": "unavailable",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": ["pressure field has not been loaded yet"],
        },
        "explanation_notes": [],
    }

    try:
        data = _load_npz(args.input)
    except FileNotFoundError:
        payload["errors"] = ["input_archive"]
        payload["violation"] = {
            "present": False,
            "kind": "missing_input",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": ["input archive not found"],
        }
        return payload
    except Exception as exc:
        payload["errors"] = [f"input_archive:{exc}"]
        payload["violation"] = {
            "present": False,
            "kind": "input_archive_error",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": [str(exc)],
        }
        return payload

    try:
        pressure, pressure_source = _load_pressure_field(data, args.frame)
    except Exception as exc:
        payload["errors"] = [f"pressure:{exc}"]
        payload["violation"] = {
            "present": False,
            "kind": "pressure_load_error",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": [str(exc)],
        }
        return payload

    if pressure is None:
        payload["errors"] = ["missing_pressure_field"]
        payload["violation"] = {
            "present": False,
            "kind": "missing_pressure_field",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": ["no pressure or pressure snapshot field was found in the archive"],
        }
        return payload

    n = int(pressure.shape[0])
    if pressure.shape[1] != n or pressure.shape[2] != n:
        payload["errors"] = [f"pressure_shape:{pressure.shape!r}"]
        payload["violation"] = {
            "present": False,
            "kind": "noncubic_pressure_field",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": [f"pressure field must be cubic, got {pressure.shape!r}"],
        }
        return payload

    try:
        domain_length, domain_source = _resolve_domain_length(data, n, args.domain_length)
    except Exception as exc:
        payload["errors"] = [f"domain_length:{exc}"]
        payload["violation"] = {
            "present": False,
            "kind": "domain_length_error",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": [str(exc)],
        }
        return payload

    laplacian_pressure = _spectral_laplacian(pressure, domain_length)
    negative_laplacian_pressure = -laplacian_pressure

    source_proxy = None
    source_proxy_source = None
    source_proxy_notes: list[str] = []

    direct_strain_sq, strain_source = _load_scalar_field(data, STRAIN_SQ_KEYS, args.frame)
    direct_omega_sq, omega_source = _load_scalar_field(data, OMEGA_SQ_KEYS, args.frame)

    if direct_strain_sq is not None and direct_omega_sq is not None:
        if direct_strain_sq.shape != pressure.shape or direct_omega_sq.shape != pressure.shape:
            payload["warnings"].append(
                f"direct proxy field shapes do not match pressure: strain={direct_strain_sq.shape!r}, omega={direct_omega_sq.shape!r}, pressure={pressure.shape!r}"
            )
        else:
            source_proxy = direct_strain_sq - 0.25 * direct_omega_sq
            source_proxy_source = f"{strain_source}-{omega_source}"
            source_proxy_notes.append("source proxy loaded from direct strain/omega square fields")
    if source_proxy is None:
        components, vector_source = _load_vector_components(data, args.frame, VELOCITY_COMPONENT_SETS)
        if components is not None and vector_source is not None:
            u, v, w = components
            if u.shape == pressure.shape and v.shape == pressure.shape and w.shape == pressure.shape:
                grad = _velocity_gradient(u, v, w, domain_length)
                strain = _strain_tensor(grad)
                omega = _vorticity_from_gradient(grad)
                source_proxy = _tensor_frobenius_squared(strain) - 0.25 * _vector_norm_squared(omega)
                source_proxy_source = f"computed_from_{vector_source}"
                source_proxy_notes.append("source proxy computed spectrally from velocity")
            else:
                payload["warnings"].append(
                    f"velocity shapes do not match pressure: u={u.shape!r}, v={v.shape!r}, w={w.shape!r}, pressure={pressure.shape!r}"
                )
        if source_proxy is None and direct_strain_sq is not None and direct_omega_sq is None:
            omega_components, omega_vector_source = _load_vector_components(data, args.frame, OMEGA_COMPONENT_SETS)
            if omega_components is not None and omega_vector_source is not None:
                omega_proxy = np.stack(omega_components, axis=0)
                if omega_proxy.shape[1:] == pressure.shape:
                    source_proxy = direct_strain_sq - 0.25 * _vector_norm_squared(omega_proxy)
                    source_proxy_source = f"{strain_source}-computed_{omega_vector_source}"
                    source_proxy_notes.append("source proxy loaded from direct strain square plus reconstructed omega norm")
                else:
                    payload["warnings"].append(
                        f"omega vector shapes do not match pressure: omega={omega_proxy.shape[1:]!r}, pressure={pressure.shape!r}"
                    )
        elif direct_omega_sq is not None and direct_strain_sq is None:
            payload["warnings"].append("omega square was present but strain square was missing")
        elif direct_strain_sq is not None and direct_omega_sq is None and source_proxy is None:
            payload["warnings"].append("strain square was present but omega square was missing")

    payload.update(
        {
            "status": OK_STATUS,
            "pressure_source": pressure_source,
            "pressure_shape": list(map(int, pressure.shape)),
            "domain_length": float(domain_length),
            "domain_length_source": domain_source,
            "laplacian_pressure_source": "spectral_fftn",
            "spectral_delta_p": {
                "min": float(np.min(laplacian_pressure)),
                "mean": float(np.mean(laplacian_pressure)),
                "max": float(np.max(laplacian_pressure)),
                "rmse_vs_zero": float(np.sqrt(np.mean(laplacian_pressure * laplacian_pressure))),
            },
            "spectral_negative_delta_p": {
                "min": float(np.min(negative_laplacian_pressure)),
                "mean": float(np.mean(negative_laplacian_pressure)),
                "max": float(np.max(negative_laplacian_pressure)),
                "rmse_vs_zero": float(np.sqrt(np.mean(negative_laplacian_pressure * negative_laplacian_pressure))),
            },
            "source_proxy_available": source_proxy is not None,
            "source_proxy_source": source_proxy_source,
            "source_proxy_notes": source_proxy_notes,
        }
    )

    if source_proxy is None:
        payload["status"] = STATUS_NO_PROXY
        payload["violation"] = {
            "present": False,
            "kind": "proxy_unavailable",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": [
                "a pressure field was available, but no strain/omega proxy could be assembled from the archive",
            ],
        }
        payload["explanation_notes"] = [
            "The script still computed the spectral pressure Laplacian, but it could not compare it against tr(S^2) - |omega|^2 / 4.",
        ]
        payload["comparisons"] = []
        payload["best_sign_proxy"] = None
        return payload

    if source_proxy.shape != pressure.shape:
        payload["errors"] = [
            f"source_proxy_shape:{source_proxy.shape!r}",
            f"pressure_shape:{pressure.shape!r}",
        ]
        payload["status"] = STATUS_MISSING_REQUIRED_FIELD
        payload["violation"] = {
            "present": False,
            "kind": "proxy_shape_mismatch",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": ["the pressure proxy and source proxy shapes do not match"],
        }
        return payload

    if not np.all(np.isfinite(source_proxy)):
        payload["errors"] = ["nonfinite_source_proxy"]
        payload["status"] = STATUS_MISSING_REQUIRED_FIELD
        payload["violation"] = {
            "present": False,
            "kind": "nonfinite_source_proxy",
            "expected_sign": "-Delta p",
            "best_sign": None,
            "notes": ["the source proxy contains non-finite values"],
        }
        return payload

    best_sign_proxy, comparisons, violation = _best_sign_proxy(source_proxy, laplacian_pressure)
    payload["best_sign_proxy"] = best_sign_proxy
    payload["comparisons"] = comparisons
    payload["violation"] = violation
    payload["explanation_notes"] = [
        "The pressure Laplacian was computed spectrally from the selected pressure frame.",
        "The source proxy compares tr(S^2) against one quarter of |omega|^2, using either direct square fields or a spectral velocity reconstruction when available.",
        (
            f"Best sign proxy: {best_sign_proxy['candidate']} with positive scale {best_sign_proxy['best_scale']:.6g}"
            if best_sign_proxy is not None
            else "No best sign proxy could be assembled."
        ),
    ]
    if violation.get("notes"):
        payload["explanation_notes"].extend(list(violation["notes"]))
    payload["warnings"] = sorted(set(payload["warnings"]))
    payload["errors"] = []
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="raw pressure NPZ or derived archive")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for 4D archives")
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="write the deterministic JSON report here",
    )
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON output")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="override the periodic domain length when metadata is missing or needs checking",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = _build_payload(args)
    text = _json_text(payload, args.pretty)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    return 0 if payload.get("status") in {OK_STATUS, STATUS_NO_PROXY} else 1


if __name__ == "__main__":
    raise SystemExit(main())
