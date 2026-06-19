#!/usr/bin/env python3
"""Pressure-Poisson bypass RHS under a selected sign convention.

This script consumes a derived NS archive, selects one component of
``{lambda2 <= beta}``, and computes the bypass RHS proxy

    rhs = 8*g12^2 + 4*(sign * delta_p)

under a requested convention:

* ``canonical_minus_delta_p`` -> ``sign = -1``
* ``plus_delta_p`` -> ``sign = +1``
* ``auto`` -> resolve from a sign-audit JSON

It reports RHS statistics, optional ``omega_norm_sq`` violations, the resolved
convention source, and whether the selected convention improves the omega
violations relative to the legacy absolute-delta proxy when that comparison is
available.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_pressure_poisson_bypass_convention_normalized.py"
CONTRACT = "ns_pressure_poisson_bypass_convention_normalized"
PRODUCER_NAME = "scripts/ns_boundary_derived_tensor_archive.py"
DEFAULT_LAMBDA2_BAND = 1.0e-3
DEFAULT_OUTPUT = Path("outputs/ns_pressure_poisson_bypass_convention_normalized.json")
OK_STATUS = "ok"
STATUS_MISSING_REQUIRED_FIELD = "missing_required_field"
STATUS_COMPONENT_NOT_FOUND = "component_not_found"
STATUS_NO_ANALYSIS_CELLS = "no_analysis_cells"

DELTA_P_KEYS = (
    "pressure_laplacian",
    "laplacian_pressure",
    "negative_laplacian_pressure",
    "delta_p",
)

OMEGA_COMPONENT_SETS = (
    ("omega_x", "omega_y", "omega_z"),
    ("omega1", "omega2", "omega3"),
    ("w_x", "w_y", "w_z"),
    ("wx", "wy", "wz"),
    ("vorticity_x", "vorticity_y", "vorticity_z"),
    ("vorticity1", "vorticity2", "vorticity3"),
)

CANONICAL_MINUS = "canonical_minus_delta_p"
PLUS_DELTA = "plus_delta_p"

CONVENTION_ALIASES = {
    "canonical-minus": CANONICAL_MINUS,
    "canonical_minus": CANONICAL_MINUS,
    "canonical_minus_delta_p": CANONICAL_MINUS,
    "minus": CANONICAL_MINUS,
    "-delta_p": CANONICAL_MINUS,
    "-deltap": CANONICAL_MINUS,
    "plus": PLUS_DELTA,
    "plus_delta_p": PLUS_DELTA,
    "+delta_p": PLUS_DELTA,
    "+deltap": PLUS_DELTA,
}


@dataclass(frozen=True)
class FieldBundle:
    lambda2: np.ndarray
    g12: np.ndarray
    delta_p: np.ndarray
    delta_p_source: str
    omega_norm_sq: np.ndarray | None
    omega_source: str | None
    beta: float
    beta_source: str
    grid_spacing: float | None
    domain_length: float | None
    scale_source: str


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


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return float(parsed)


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def _authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "diagnostic_only": True,
        "empirical_non_promoting": True,
        "pressure_bypass_proof": False,
        "convention_normalization_theorem": False,
        "clay_navier_stokes_promoted": False,
        "terminal_promotion": False,
    }


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in payload:
        try:
            meta = json.loads(str(np.asarray(payload["meta_json"]).item()))
        except Exception as exc:  # pragma: no cover - defensive path.
            raise ValueError(f"meta_json could not be parsed as JSON: {exc}") from exc
        if isinstance(meta, dict):
            for name in ("domain_length", "grid_spacing", "N", "axis_order", "length"):
                if name in meta and name not in payload:
                    payload[name] = np.asarray(meta[name])
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


def _load_omega_norm_sq(
    data: dict[str, np.ndarray],
    lambda2_shape: tuple[int, int, int],
    frame: int | None,
) -> tuple[np.ndarray | None, str | None]:
    if "omega_norm_sq" in data:
        return _load_frame_field("omega_norm_sq", data["omega_norm_sq"], frame), "omega_norm_sq"

    for key_set in OMEGA_COMPONENT_SETS:
        if all(key in data for key in key_set):
            components = [_load_frame_field(f"omega component {key}", data[key], frame) for key in key_set]
            for key, arr in zip(key_set, components):
                if arr.shape != lambda2_shape:
                    raise ValueError(
                        f"omega component {key} shape {arr.shape!r} does not match lambda2 {lambda2_shape!r}"
                    )
            if any(not np.all(np.isfinite(arr)) for arr in components):
                raise ValueError("omega component contains non-finite values")
            return components[0] * components[0] + components[1] * components[1] + components[2] * components[2], "+".join(key_set)

    return None, None


def _load_delta_p_source(
    data: dict[str, np.ndarray],
    lambda2_shape: tuple[int, int, int],
    frame: int | None,
) -> tuple[np.ndarray, str]:
    for key in DELTA_P_KEYS:
        if key not in data:
            continue
        delta_p = _load_frame_field(key, data[key], frame)
        if delta_p.shape != lambda2_shape:
            raise ValueError(f"{key} shape {delta_p.shape!r} does not match lambda2 {lambda2_shape!r}")
        return delta_p, key

    pressure_key = "pressure" if "pressure" in data else "p"
    if pressure_key not in data:
        raise KeyError("missing_pressure_field")
    pressure = _load_frame_field(pressure_key, data[pressure_key], frame)
    if pressure.shape != lambda2_shape:
        raise ValueError(f"pressure shape {pressure.shape!r} does not match lambda2 {lambda2_shape!r}")
    return pressure, "pressure"


def _spectral_laplacian(field: np.ndarray, length: float) -> np.ndarray:
    n = int(field.shape[0])
    freq = 2.0 * np.pi * np.fft.fftfreq(n, d=length / float(n))
    kx = freq.reshape(n, 1, 1)
    ky = freq.reshape(1, n, 1)
    kz = freq.reshape(1, 1, n)
    k2 = (kx * kx) + (ky * ky) + (kz * kz)
    transformed = np.fft.fftn(field, axes=(0, 1, 2))
    return np.fft.ifftn(-k2 * transformed, axes=(0, 1, 2)).real


def _resolve_scale(
    lambda2_shape: tuple[int, int, int],
    data: dict[str, np.ndarray],
) -> tuple[float | None, float | None, str]:
    grid_spacing_value, _ = _scalar_metadata(data, "grid_spacing")
    domain_length_value, _ = _scalar_metadata(data, "domain_length", "length")

    grid_spacing = None
    domain_length = None
    scale_source = "index_units"
    n = float(lambda2_shape[0])

    if grid_spacing_value is not None:
        grid_spacing = _finite_float(grid_spacing_value, "grid_spacing")
        if grid_spacing <= 0.0:
            raise ValueError("grid_spacing must be positive")
        scale_source = "grid_spacing"
        if domain_length_value is not None:
            domain_length = _finite_float(domain_length_value, "domain_length")
            if domain_length <= 0.0:
                raise ValueError("domain_length must be positive")
            if not math.isclose(domain_length, grid_spacing * n, rel_tol=1.0e-12, abs_tol=1.0e-12):
                raise ValueError("grid_spacing and domain_length mismatch")
        else:
            domain_length = grid_spacing * n
    elif domain_length_value is not None:
        domain_length = _finite_float(domain_length_value, "domain_length")
        if domain_length <= 0.0:
            raise ValueError("domain_length must be positive")
        grid_spacing = domain_length / n
        scale_source = "domain_length"

    return (
        None if grid_spacing is None else float(grid_spacing),
        None if domain_length is None else float(domain_length),
        scale_source,
    )


def _load_bundle(path: Path, frame: int | None) -> tuple[FieldBundle | None, list[str], list[str]]:
    missing: list[str] = []
    warnings: list[str] = []

    try:
        data = _load_npz(path)
    except FileNotFoundError:
        return None, ["input_archive"], []
    except Exception as exc:
        return None, [f"input_archive:{exc}"], []

    try:
        lambda2 = _load_frame_field("lambda2", data["lambda2"], frame)
        g12 = _load_frame_field("g12", data["g12"], frame)
    except KeyError as exc:
        return None, [f"missing_required_field:{exc}"], []
    except Exception as exc:
        return None, [f"field_cast:{exc}"], []

    if not np.all(np.isfinite(lambda2)) or not np.all(np.isfinite(g12)):
        return None, ["nonfinite_required_field"], []

    if lambda2.shape != g12.shape:
        return None, ["shape_mismatch:lambda2,g12"], []

    beta_source = "archive"
    try:
        if "beta" in data:
            beta_value = _finite_float(np.asarray(data["beta"]).item(), "beta")
        else:
            missing.append("beta")
            beta_value = 0.0
    except Exception as exc:
        missing.append(f"beta:{exc}")
        beta_value = 0.0

    try:
        grid_spacing, domain_length, scale_source = _resolve_scale(lambda2.shape, data)
    except Exception as exc:
        return None, [f"scale_metadata:{exc}"], []

    try:
        delta_p_field, delta_p_source = _load_delta_p_source(data, lambda2.shape, frame)
    except Exception as exc:
        return None, [f"delta_p:{exc}"], []

    if delta_p_source == "pressure":
        if domain_length is None:
            return None, ["missing_domain_length_or_grid_spacing_for_pressure_laplacian"], []
        if grid_spacing is None:
            warnings.append("grid_spacing_missing_for_pressure_laplacian; deriving from pressure and domain_length only")
        delta_p_field = _spectral_laplacian(delta_p_field, domain_length)
        delta_p_source = "spectral_laplacian_pressure"

    if delta_p_field.shape != lambda2.shape:
        return None, ["shape_mismatch:delta_p,lambda2"], []
    if not np.all(np.isfinite(delta_p_field)):
        return None, ["nonfinite_delta_p"], []

    omega_norm_sq: np.ndarray | None = None
    omega_source: str | None = None
    try:
        omega_norm_sq, omega_source = _load_omega_norm_sq(data, lambda2.shape, frame)
    except Exception as exc:  # pragma: no cover - optional field parse path.
        warnings.append(f"omega_norm_sq_unavailable:{exc}")

    if omega_norm_sq is not None and not np.all(np.isfinite(omega_norm_sq)):
        warnings.append("nonfinite_omega_norm_sq")
        omega_norm_sq = None
        omega_source = None

    if missing:
        return None, sorted(set(missing)), warnings

    return (
        FieldBundle(
            lambda2=lambda2,
            g12=g12,
            delta_p=delta_p_field,
            delta_p_source=delta_p_source,
            omega_norm_sq=omega_norm_sq,
            omega_source=omega_source,
            beta=float(beta_value),
            beta_source=beta_source,
            grid_spacing=grid_spacing,
            domain_length=domain_length,
            scale_source=scale_source,
        ),
        [],
        warnings,
    )


def _label_components(mask: np.ndarray) -> np.ndarray:
    active = np.asarray(mask, dtype=bool)
    try:  # pragma: no cover - optional dependency.
        from scipy.ndimage import label as scipy_label
        from scipy.ndimage import generate_binary_structure as scipy_binary_structure
    except Exception:  # pragma: no cover
        scipy_label = None
        scipy_binary_structure = None

    if scipy_label is not None and scipy_binary_structure is not None:
        structure = scipy_binary_structure(3, 1)
        labels, _ = scipy_label(active, structure=structure)
        return np.asarray(labels, dtype=np.int32)

    shape = active.shape
    labels = np.zeros(shape, dtype=np.int32)
    if not np.any(active):
        return labels

    visited = np.zeros(shape, dtype=bool)
    component_id = 0
    starts = np.argwhere(active)
    for start in starts:
        x, y, z = (int(start[0]), int(start[1]), int(start[2]))
        if visited[x, y, z]:
            continue
        component_id += 1
        stack = [(x, y, z)]
        visited[x, y, z] = True
        labels[x, y, z] = component_id
        while stack:
            cx, cy, cz = stack.pop()
            for nx, ny, nz in (
                (cx - 1, cy, cz),
                (cx + 1, cy, cz),
                (cx, cy - 1, cz),
                (cx, cy + 1, cz),
                (cx, cy, cz - 1),
                (cx, cy, cz + 1),
            ):
                if nx < 0 or ny < 0 or nz < 0:
                    continue
                if nx >= shape[0] or ny >= shape[1] or nz >= shape[2]:
                    continue
                if active[nx, ny, nz] and not visited[nx, ny, nz]:
                    visited[nx, ny, nz] = True
                    labels[nx, ny, nz] = component_id
                    stack.append((nx, ny, nz))
    return labels


def _select_component(
    labels: np.ndarray,
    component_id: int | None,
    lambda2: np.ndarray,
    lambda2_band: float,
) -> tuple[int | None, str | None]:
    component_count = int(labels.max())
    if component_count == 0:
        return None, None

    if component_id is not None:
        if component_id > component_count:
            return None, "requested_component_not_found"
        if not np.any(labels == component_id):
            return None, "requested_component_not_found"
        return int(component_id), "requested"

    component_cells = np.bincount(labels.ravel(), minlength=component_count + 1)
    boundary_counts = np.zeros(component_count, dtype=np.int64)
    for cid in range(1, component_count + 1):
        boundary_counts[cid - 1] = int(np.count_nonzero((labels == cid) & (np.abs(lambda2) <= lambda2_band)))

    if np.any(boundary_counts > 0):
        idx = int(np.argmax(boundary_counts))
        return int(idx + 1), "largest_boundary_component"

    idx = int(np.argmax(component_cells[1:]))
    return int(idx + 1), "largest_component"


def _stats(values: np.ndarray, mask: np.ndarray) -> dict[str, float] | None:
    if not np.any(mask):
        return None
    subset = np.asarray(values, dtype=np.float64)[mask]
    if subset.size == 0:
        return None
    return {
        "cell_count": int(subset.size),
        "min": float(np.min(subset)),
        "mean": float(np.mean(subset)),
        "max": float(np.max(subset)),
        "sum": float(np.sum(subset)),
    }


def _load_sign_audit(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError("sign audit JSON must contain an object at top level")
    return payload


def _normalize_convention(value: str) -> str:
    normalized = value.strip().lower().replace(" ", "_")
    if normalized in CONVENTION_ALIASES:
        return CONVENTION_ALIASES[normalized]
    if normalized in {CANONICAL_MINUS, PLUS_DELTA, "auto"}:
        return normalized
    raise ValueError(f"unsupported convention {value!r}")


def _convention_sign(convention: str) -> float:
    if convention == CANONICAL_MINUS:
        return -1.0
    if convention == PLUS_DELTA:
        return 1.0
    raise ValueError(f"unsupported resolved convention {convention!r}")


def _candidate_to_convention(candidate: Any, source: str) -> tuple[str, str] | None:
    if candidate is None:
        return None
    text = str(candidate).strip().lower()
    if text in {CANONICAL_MINUS, "minus", "-delta p", "-delta_p", "-deltap"}:
        return CANONICAL_MINUS, source
    if text in {PLUS_DELTA, "plus", "+delta p", "+delta_p", "+deltap"}:
        return PLUS_DELTA, source
    return None


def _resolve_auto_convention(sign_audit_json: Path | None) -> tuple[str | None, str | None, list[str]]:
    warnings: list[str] = []
    if sign_audit_json is None:
        return None, None, ["sign_audit_json_required_for_auto_convention"]

    try:
        audit = _load_sign_audit(sign_audit_json)
    except FileNotFoundError:
        return None, None, [f"sign_audit_json:{sign_audit_json}"]
    except Exception as exc:
        return None, None, [f"sign_audit_json:{exc}"]

    for path in (
        ("best_sign_proxy", "candidate"),
        ("best_sign_proxy", "sign"),
        ("violation", "best_sign"),
        ("resolved_convention",),
        ("convention",),
    ):
        node: Any = audit
        try:
            for key in path:
                node = node[key]
        except Exception:
            continue

        resolved = _candidate_to_convention(node, f"sign_audit_json.{'.'.join(path)}")
        if resolved is None and len(path) == 1 and isinstance(node, str):
            try:
                normalized = _normalize_convention(node)
            except Exception:
                normalized = None
            if normalized in {CANONICAL_MINUS, PLUS_DELTA}:
                return normalized, f"sign_audit_json.{path[0]}", warnings
            continue
        if resolved is not None:
            return resolved[0], resolved[1], warnings

    return None, None, ["sign_audit_json_did_not_contain_a_resolvable_sign"]


def _build_rhs_proxy(
    bundle: FieldBundle,
    sign_factor: float,
    analysis_mask: np.ndarray,
) -> tuple[np.ndarray, dict[str, float] | None]:
    rhs_proxy = 8.0 * bundle.g12 * bundle.g12 + 4.0 * sign_factor * bundle.delta_p
    return rhs_proxy, _stats(rhs_proxy, analysis_mask)


def _comparison_payload(
    omega_norm_sq: np.ndarray,
    rhs_proxy: np.ndarray,
    analysis_mask: np.ndarray,
) -> dict[str, Any]:
    omega_stats = _stats(omega_norm_sq, analysis_mask)
    if omega_stats is None:
        return {
            "source": "omega_norm_sq",
            "stats": None,
            "violation_count": None,
            "max_violation": None,
            "omega_leq_rhs_cells": None,
            "ratio_violation": None,
            "violation_mask_source": "omega_norm_sq > rhs_proxy",
        }

    violation = np.zeros_like(rhs_proxy, dtype=np.float64)
    violation_mask = omega_norm_sq > rhs_proxy
    violation[violation_mask] = omega_norm_sq[violation_mask] - rhs_proxy[violation_mask]
    violation_mask &= analysis_mask
    violation_count = int(np.count_nonzero(violation_mask))
    analysis_cell_count = int(np.count_nonzero(analysis_mask))

    return {
        "source": "omega_norm_sq",
        "stats": omega_stats,
        "violation_count": violation_count,
        "max_violation": None if violation_count == 0 else float(np.max(np.asarray(violation[violation_mask], dtype=np.float64))),
        "omega_leq_rhs_cells": analysis_cell_count - violation_count,
        "ratio_violation": float(violation_count / analysis_cell_count) if analysis_cell_count else None,
        "violation_mask_source": "omega_norm_sq > rhs_proxy",
    }


def _omega_available(bundle: FieldBundle) -> bool:
    return bundle.omega_norm_sq is not None


def _build_payload(args: argparse.Namespace) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "producer": PRODUCER_NAME,
        "input": str(args.derived_archive),
        "frame": args.frame,
        "component_id": int(args.component_id) if args.component_id is not None else None,
        "component_selector": None,
        "requested_component_id": int(args.component_id) if args.component_id is not None else None,
        "lambda2_band": float(args.lambda2_band),
        "requested_convention": args.convention,
        "sign_audit_json": None if args.sign_audit_json is None else str(args.sign_audit_json),
        "authority": _authority(),
        "warnings": [],
        "errors": [],
        "O": "Normalize the pressure bypass RHS under a selected sign convention from a derived NS archive.",
        "R": "Resolve canonical-minus, plus, or audit-selected pressure convention and report RHS/omega comparison evidence.",
        "C": SCRIPT_NAME,
        "S": "Load scalar tensor fields from a derived NPZ, select a boundary component, and compare signed RHS proxies against omega norms.",
        "L": "Status is ok only when a requested or auto-selected component exists and the analysis mask is non-empty.",
        "P": "Emit a convention-normalized bypass proxy and quantify whether the resolved sign improves omega violations over |delta_p|.",
        "G": "Authority stays false and no theorem or promotion claim is made.",
        "F": "Missing required fields, unresolved auto convention, or an empty analysis mask block a closed report.",
        "scale_source": "index_units",
    }

    if args.lambda2_band < 0.0 or not math.isfinite(args.lambda2_band):
        payload["status"] = STATUS_MISSING_REQUIRED_FIELD
        payload["errors"] = ["invalid_lambda2_band"]
        payload["warnings"] = []
        return payload

    bundle, load_errors, load_warnings = _load_bundle(args.derived_archive, args.frame)
    payload["warnings"].extend(load_warnings)
    if bundle is None:
        payload["status"] = STATUS_MISSING_REQUIRED_FIELD
        payload["errors"] = sorted(set(load_errors))
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload["grid_spacing"] = None if bundle.grid_spacing is None else float(bundle.grid_spacing)
    payload["domain_length"] = None if bundle.domain_length is None else float(bundle.domain_length)
    payload["scale_source"] = bundle.scale_source
    payload["shape"] = [int(v) for v in bundle.lambda2.shape]
    payload["beta"] = float(bundle.beta)
    payload["beta_source"] = bundle.beta_source
    payload["delta_p_source"] = bundle.delta_p_source

    labels = _label_components(bundle.lambda2 <= bundle.beta)
    component_count = int(labels.max())
    payload["component_count"] = component_count
    selected_component, component_selector = _select_component(labels, args.component_id, bundle.lambda2, float(args.lambda2_band))
    payload["component_selector"] = component_selector

    if selected_component is None:
        payload["status"] = STATUS_COMPONENT_NOT_FOUND
        payload["errors"] = ["component_not_found"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    component_mask = labels == selected_component
    if not np.any(component_mask):
        payload["status"] = STATUS_COMPONENT_NOT_FOUND
        payload["errors"] = ["component_mask_empty"]
        payload["component_id"] = int(selected_component)
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload["component_id"] = int(selected_component)
    component_cell_count = int(np.count_nonzero(component_mask))
    payload["component_cell_count"] = component_cell_count

    boundary_mask = component_mask & (np.abs(bundle.lambda2) <= float(args.lambda2_band))
    tight_mask = component_mask & (bundle.lambda2 <= bundle.beta)
    if np.any(boundary_mask):
        analysis_mask = boundary_mask
        payload["analysis_mask_source"] = "boundary_abs_lambda2_band"
    else:
        analysis_mask = tight_mask
        payload["analysis_mask_source"] = "tight_component_beta_mask"
        payload["warnings"].append("boundary_mask_empty_fallback_to_tight_band")

    if not np.any(analysis_mask):
        payload["status"] = STATUS_NO_ANALYSIS_CELLS
        payload["errors"] = ["analysis_mask_empty"]
        payload["boundary_cell_count"] = int(np.count_nonzero(boundary_mask))
        payload["tight_band_cell_count"] = int(np.count_nonzero(tight_mask))
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload["boundary_cell_count"] = int(np.count_nonzero(boundary_mask))
    payload["tight_band_cell_count"] = int(np.count_nonzero(tight_mask))
    payload["analysis_cell_count"] = int(np.count_nonzero(analysis_mask))

    sign_audit_resolution_warnings: list[str] = []
    resolved_convention = None
    convention_source = None

    try:
        requested_convention = _normalize_convention(args.convention)
    except Exception as exc:
        payload["status"] = STATUS_MISSING_REQUIRED_FIELD
        payload["errors"] = [f"invalid_convention:{exc}"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    if requested_convention == "auto":
        resolved_convention, convention_source, sign_audit_resolution_warnings = _resolve_auto_convention(args.sign_audit_json)
        payload["warnings"].extend(sign_audit_resolution_warnings)
        if resolved_convention is None:
            payload["status"] = STATUS_MISSING_REQUIRED_FIELD
            payload["errors"] = ["sign_audit_json_required_or_unresolvable_for_auto_convention"]
            payload["warnings"] = sorted(set(payload["warnings"]))
            return payload
    else:
        resolved_convention = requested_convention
        convention_source = f"cli:{requested_convention}"

    sign_factor = _convention_sign(resolved_convention)
    payload["convention"] = resolved_convention
    payload["convention_factor"] = float(sign_factor)
    payload["convention_source"] = convention_source

    rhs_proxy, rhs_stats = _build_rhs_proxy(bundle, sign_factor, analysis_mask)
    if rhs_stats is None:
        payload["status"] = STATUS_NO_ANALYSIS_CELLS
        payload["errors"] = ["analysis_stats_unavailable"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload.update(
        {
            "status": OK_STATUS,
            "rhs_proxy_stats": rhs_stats,
            "rhs_proxy_sum": float(np.sum(rhs_proxy[analysis_mask])),
            "rhs_proxy_formula": f"8*g12^2 + 4*({sign_factor:+.0f})*delta_p",
            "omega_norm_sq_available": _omega_available(bundle),
        }
    )

    if _omega_available(bundle) and bundle.omega_norm_sq is not None:
        payload["omega_norm_sq"] = _comparison_payload(bundle.omega_norm_sq, rhs_proxy, analysis_mask)
    else:
        payload["omega_norm_sq"] = None
        payload["warnings"].append("omega_norm_sq_unavailable")

    absolute_delta_proxy: np.ndarray | None = None
    absolute_delta_stats: dict[str, float] | None = None
    absolute_comparison: dict[str, Any] | None = None
    improved: bool | None = None

    if bundle.delta_p is not None:
        absolute_delta_proxy = 8.0 * bundle.g12 * bundle.g12 + 4.0 * np.abs(bundle.delta_p)
        absolute_delta_stats = _stats(absolute_delta_proxy, analysis_mask)
        payload["absolute_delta_proxy_stats"] = absolute_delta_stats
        payload["absolute_delta_proxy_sum"] = float(np.sum(absolute_delta_proxy[analysis_mask]))
        payload["absolute_delta_proxy_formula"] = "8*g12^2 + 4*abs(delta_p)"

        if bundle.omega_norm_sq is not None:
            absolute_comparison = _comparison_payload(bundle.omega_norm_sq, absolute_delta_proxy, analysis_mask)
            payload["absolute_delta_proxy_omega_norm_sq"] = absolute_comparison
            if (
                isinstance(payload["omega_norm_sq"], dict)
                and payload["omega_norm_sq"].get("violation_count") is not None
                and absolute_comparison.get("violation_count") is not None
            ):
                selected_count = int(payload["omega_norm_sq"]["violation_count"])
                baseline_count = int(absolute_comparison["violation_count"])
                if selected_count < baseline_count:
                    improved = True
                elif selected_count > baseline_count:
                    improved = False
                else:
                    selected_max = payload["omega_norm_sq"].get("max_violation")
                    baseline_max = absolute_comparison.get("max_violation")
                    if selected_max is None or baseline_max is None:
                        improved = None
                    else:
                        improved = float(selected_max) < float(baseline_max)

    payload["violations_improve_vs_absolute_delta_proxy"] = improved
    payload["improvement_comparison_available"] = absolute_comparison is not None

    payload["warnings"] = sorted(set(payload["warnings"]))
    payload["errors"] = []
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--derived-archive", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for 4D archives")
    parser.add_argument("--component-id", type=_positive_int, default=None, help="target component id; defaults to auto")
    parser.add_argument(
        "--lambda2-band",
        type=float,
        default=DEFAULT_LAMBDA2_BAND,
        help="absolute lambda2 boundary band for analysis",
    )
    parser.add_argument(
        "--convention",
        type=str,
        default="auto",
        help="pressure convention: auto, canonical-minus, or plus",
    )
    parser.add_argument(
        "--sign-audit-json",
        type=Path,
        default=None,
        help="optional sign audit JSON used when --convention=auto",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="write payload to JSON file",
    )
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON output.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = _build_payload(args)
    text = _json_text(payload, bool(args.pretty))
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    return 0 if payload.get("status") == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
