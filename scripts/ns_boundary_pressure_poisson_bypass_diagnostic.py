#!/usr/bin/env python3
"""Pressure-Poisson bypass diagnostic on NS boundary components.

This diagnostic consumes a derived tensor archive in NPZ form and inspects one
component of ``{lambda2 <= beta}``, reporting:

- pressure Poisson RHS proxy fields (``delta_p`` / laplacian source),
- statistics for ``g12`` and available/derived ``lambda3``,
- analysis-mask area proxy,
- pressure Poisson bypass proxy ``rhs = 8*g12^2 + 4*abs(delta_p)``,
- optional ``omega_norm_sq`` comparison against the bypass rhs.

The diagnostic is fail-closed and emits deterministic JSON-only output.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_boundary_pressure_poisson_bypass_diagnostic.py"
CONTRACT = "ns_boundary_pressure_poisson_bypass_diagnostic"
PRODUCER_NAME = "scripts/ns_boundary_derived_tensor_archive.py"
ROUTE_DECISION = "FAIL_CLOSED_PRESSURE_POISSON_BYPASS_DIAGNOSTIC"
DEFAULT_LAMBDA2_BAND = 1.0e-6
DEFAULT_OUTPUT = Path("outputs/ns_boundary_pressure_poisson_bypass_diagnostic.json")
OK_STATUS = "ok"
STATUS_MISSING = "missing_required_field"
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


@dataclass(frozen=True)
class FieldBundle:
    lambda2: np.ndarray
    g12: np.ndarray
    lambda3: np.ndarray
    lambda3_source: str
    delta_p: np.ndarray
    delta_p_source: str
    beta: float
    beta_source: str
    omega_norm_sq: np.ndarray | None
    omega_source: str | None
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


def _json_text(payload: dict[str, Any]) -> str:
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


def _load_delta_p_source(data: dict[str, np.ndarray], lambda2_shape: tuple[int, int, int], frame: int | None) -> tuple[
    np.ndarray,
    str,
]:
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


def _load_bundle(
    path: Path,
    frame: int | None,
    beta_override: float | None,
) -> tuple[FieldBundle | None, list[str], list[str]]:
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
        if beta_override is not None:
            beta_value = _finite_float(beta_override, "--beta")
            beta_source = "cli"
        elif "beta" in data:
            beta_value = _finite_float(np.asarray(data["beta"]).item(), "beta")
        else:
            missing.append("beta")
            beta_value = 0.0
    except Exception as exc:
        missing.append(f"beta:{exc}")
        beta_value = 0.0

    if "lambda3" in data:
        try:
            lambda3 = _load_frame_field("lambda3", data["lambda3"], frame)
            lambda3_source = "lambda3"
        except Exception as exc:
            return None, [f"field_cast_lambda3:{exc}"], []
    else:
        lambda3 = g12 - 2.0 * lambda2
        lambda3_source = "derived_from_g12_minus_2_lambda2"
    if lambda3.shape != lambda2.shape:
        return None, ["shape_mismatch:lambda3,lambda2"], []
    if not np.all(np.isfinite(lambda3)):
        return None, ["nonfinite_lambda3"], []

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
            # keep non-fatal warning; spectral derivative still uses domain_length
            warnings.append("grid_spacing_missing_for_pressure_laplacian; deriving from pressure and domain_length only")
        delta_p_field = _spectral_laplacian(delta_p_field, domain_length)
        delta_p_source = "spectral_laplacian_pressure"
    elif delta_p_source in DELTA_P_KEYS:
        # already provided in archive
        pass

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
            lambda3=lambda3,
            lambda3_source=lambda3_source,
            delta_p=delta_p_field,
            delta_p_source=delta_p_source,
            beta=float(beta_value),
            beta_source=beta_source,
            omega_norm_sq=omega_norm_sq,
            omega_source=omega_source,
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
        "authority": _authority(),
        "warnings": [],
        "errors": [],
        "O": "Emit fail-closed pressure-Poisson bypass diagnostics from derived NS boundary archives.",
        "R": "Select a {lambda2<=beta} boundary component and report g12/lambda3/delta_p/RHS/omega checks.",
        "C": SCRIPT_NAME,
        "S": "Load scalar tensor fields from a derived NPZ, select a boundary component, and fail on invalid inputs or empty analysis layers.",
        "L": "Status is ok only when a requested/requested-or-auto component exists and the analysis mask is non-empty.",
        "P": ROUTE_DECISION,
        "G": "No theorem claim is made; this is empirical boundary telemetry only.",
        "F": "Evidence-only diagnostic; empirical/Clay/theorem authority and promotions remain false.",
        "scale_source": "index_units",
    }

    if args.lambda2_band < 0.0 or not math.isfinite(args.lambda2_band):
        payload["status"] = STATUS_MISSING
        payload["errors"] = ["invalid_lambda2_band"]
        payload["warnings"] = []
        return payload

    if args.beta is not None:
        try:
            _finite_float(args.beta, "--beta")
        except Exception as exc:
            payload["status"] = STATUS_MISSING
            payload["errors"] = [f"invalid_beta:{exc}"]
            payload["warnings"] = []
            return payload

    bundle, load_errors, load_warnings = _load_bundle(args.derived_archive, args.frame, args.beta)
    payload["warnings"].extend(load_warnings)
    if bundle is None:
        payload["status"] = STATUS_MISSING
        payload["errors"] = sorted(set(load_errors))
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload["grid_spacing"] = None if bundle.grid_spacing is None else float(bundle.grid_spacing)
    payload["domain_length"] = None if bundle.domain_length is None else float(bundle.domain_length)
    payload["scale_source"] = bundle.scale_source
    payload["shape"] = [int(v) for v in bundle.lambda2.shape]
    payload["beta"] = float(bundle.beta)
    payload["beta_source"] = bundle.beta_source

    if not np.all(np.isfinite(bundle.lambda2)) or not np.all(np.isfinite(bundle.g12)):
        payload["status"] = STATUS_MISSING
        payload["errors"] = ["nonfinite_required_field"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

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

    analysis_cell_count = int(np.count_nonzero(analysis_mask))
    analysis_stats_g12 = _stats(bundle.g12, analysis_mask)
    analysis_stats_lambda3 = _stats(bundle.lambda3, analysis_mask)
    analysis_stats_delta_p = _stats(bundle.delta_p, analysis_mask)
    rhs_proxy = 8.0 * bundle.g12 * bundle.g12 + 4.0 * np.abs(bundle.delta_p)
    rhs_stats = _stats(rhs_proxy, analysis_mask)
    if analysis_stats_g12 is None or rhs_stats is None:
        payload["status"] = STATUS_NO_ANALYSIS_CELLS
        payload["errors"] = ["analysis_stats_unavailable"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload.update(
        {
            "status": OK_STATUS,
            "boundary_cell_count": int(np.count_nonzero(boundary_mask)),
            "tight_band_cell_count": int(np.count_nonzero(tight_mask)),
            "analysis_cell_count": analysis_cell_count,
            "g12_stats": analysis_stats_g12,
            "lambda3_source": bundle.lambda3_source,
            "lambda3_stats": analysis_stats_lambda3,
            "delta_p_source": bundle.delta_p_source,
            "delta_p_stats": analysis_stats_delta_p,
            "rhs_proxy_stats": rhs_stats,
            "rhs_proxy_sum": float(np.sum(rhs_proxy[analysis_mask])),
            "area_proxy_cell_count": analysis_cell_count,
            "area_proxy_physical": None
            if bundle.grid_spacing is None
            else float(float(analysis_cell_count) * bundle.grid_spacing * bundle.grid_spacing),
            "analysis_mask_sum_g12_abs": float(np.sum(np.abs(bundle.g12[analysis_mask]))),
        }
    )

    if bundle.omega_norm_sq is None:
        payload["warnings"].append("omega_norm_sq_unavailable")
    else:
        omega_stats = _stats(bundle.omega_norm_sq, analysis_mask)
        violation = np.zeros_like(rhs_proxy, dtype=np.float64)
        violation_mask = bundle.omega_norm_sq > rhs_proxy
        violation[violation_mask] = bundle.omega_norm_sq[violation_mask] - rhs_proxy[violation_mask]
        violation_mask &= analysis_mask
        violation_count = int(np.count_nonzero(violation_mask))
        payload["omega_norm_sq"] = {
            "source": str(bundle.omega_source),
            "stats": omega_stats,
            "violation_count": violation_count,
            "max_violation": None
            if violation_count == 0
            else float(np.max(np.asarray(violation[violation_mask], dtype=np.float64))),
            "omega_leq_rhs_cells": analysis_cell_count - violation_count,
            "ratio_violation": float(violation_count / analysis_cell_count),
            "violation_mask_source": "omega_norm_sq > rhs_proxy",
        }

    payload["warnings"] = sorted(set(payload["warnings"]))
    payload["errors"] = []
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--derived-archive", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for 4D archives")
    parser.add_argument("--component-id", type=_positive_int, default=None, help="target component id; defaults to auto")
    parser.add_argument("--lambda2-band", type=float, default=DEFAULT_LAMBDA2_BAND, help="absolute lambda2 boundary band for analysis")
    parser.add_argument("--beta", type=float, default=None, help="override beta threshold")
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
    text = _json_text(payload) if not args.pretty else json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + ("\n" if args.pretty else ""), encoding="utf-8")
    return 0 if payload.get("status") == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
