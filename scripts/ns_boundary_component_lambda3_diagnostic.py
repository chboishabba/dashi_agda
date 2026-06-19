#!/usr/bin/env python3
"""Lambda3 boundary diagnostics for derived NS tensor archives.

This script consumes an existing derived archive produced by
``scripts/ns_boundary_derived_tensor_archive.py`` and inspects one connected
component of ``{lambda2 <= beta}``, reporting lambda3 statistics on the
boundary layer ``|lambda2| <= lambda2_band`` when present and on the tight
component layer otherwise.

The diagnostic is fail-closed and emits deterministic JSON.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_boundary_component_lambda3_diagnostic.py"
CONTRACT = "ns_boundary_component_lambda3_diagnostic"
PRODUCER_NAME = "scripts/ns_boundary_derived_tensor_archive.py"
DEFAULT_LAMBDA2_BAND = 1.0e-6
DEFAULT_DELTA = 1.0e-8
DEFAULT_LAMBDA3_QUANTILES = (0.0, 0.25, 0.5, 0.75, 1.0)
OK_STATUS = "ok"
ROUTE_DECISION = "FAIL_CLOSED_LAMBDA3_COMPONENT_DIAGNOSTIC"
STATUS_COMPONENT_NOT_FOUND = "component_not_found"
STATUS_NO_ANALYSIS_CELLS = "no_analysis_cells"
STATUS_MISSING = "missing_required_field"

try:  # Optional dependency.
    from scipy.ndimage import label as scipy_label
    from scipy.ndimage import generate_binary_structure as scipy_binary_structure
except Exception:  # pragma: no cover - optional dependency.
    scipy_label = None
    scipy_binary_structure = None


@dataclass(frozen=True)
class FieldBundle:
    lambda2: np.ndarray
    g12: np.ndarray
    lambda3: np.ndarray
    b_k: np.ndarray
    pressure_hessian_norm: np.ndarray | None
    rho: np.ndarray | None
    beta: float
    beta_source: str
    lambda3_source: str
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
    return parsed


def _finite_nonnegative_float(value: Any, name: str) -> float:
    parsed = _finite_float(value, name)
    if parsed < 0.0:
        raise ValueError(f"{name} must be nonnegative")
    return parsed


def _finite_nonnegative_arg(value: str) -> float:
    try:
        return _finite_nonnegative_float(value, "argument")
    except ValueError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def _finite_probability(value: str) -> float:
    parsed = _finite_float(value, "quantile")
    if not (0.0 <= parsed <= 1.0):
        raise argparse.ArgumentTypeError("quantile must be in [0,1]")
    return parsed


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


def _scalar_metadata(data: dict[str, np.ndarray], *names: str) -> tuple[Any | None, str | None]:
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


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}

    if "meta_json" in payload:
        try:
            meta = json.loads(str(np.asarray(payload["meta_json"]).item()))
        except Exception as exc:
            raise ValueError(f"meta_json could not be parsed as JSON: {exc}") from exc
        if isinstance(meta, dict):
            for key in ("domain_length", "grid_spacing", "N", "axis_order", "length"):
                if key in meta and key not in payload:
                    payload[key] = np.asarray(meta[key])
    return payload


def _load_frame_field(name: str, value: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(value, dtype=np.float64)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) != 1:
                raise ValueError(f"{name} is 4D with {arr.shape[0]} frames; pass --frame")
            arr = arr[0]
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {arr.shape[0]} frames")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be 3D after frame selection, got {arr.shape!r}")
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} contains non-finite values")
    return arr


def _choose_lambda3_source(
    data: dict[str, np.ndarray], lambda2: np.ndarray, g12: np.ndarray, frame: int | None
) -> tuple[np.ndarray, str]:
    if "lambda3" in data:
        lambda3 = _load_frame_field("lambda3", data["lambda3"], frame)
        return lambda3, "lambda3"
    return np.asarray(g12 - 2.0 * lambda2, dtype=np.float64), "derived_from_lambda2_g12"


def _load_fields(
    path: Path,
    frame: int | None,
    beta_override: float | None,
    strict: bool,
) -> tuple[FieldBundle | None, list[str], list[str]]:
    missing: list[str] = []
    warnings: list[str] = []

    try:
        data = _load_npz(path)
    except FileNotFoundError:
        return None, ["input_archive"], []
    except Exception as exc:
        return None, [f"input_archive:{exc}"], []

    b_key = "B_k" if "B_k" in data else "B_k_max" if "B_k_max" in data else "B_k"
    for key in ("lambda2", "g12", b_key):
        if key not in data:
            missing.append(key)

    beta_source = "archive"
    try:
        if beta_override is not None:
            beta_value = _finite_float(beta_override, "--beta")
            beta_source = "cli"
        elif "beta" in data:
            beta_value = _finite_float(np.asarray(data["beta"]).item(), "beta")
        else:
            beta_value = 0.0
            missing.append("beta")
    except Exception as exc:
        missing.append(f"beta:{exc}")
        beta_value = 0.0

    if missing:
        return None, sorted(set(missing)), warnings

    try:
        lambda2 = _load_frame_field("lambda2", np.asarray(data["lambda2"], dtype=np.float64), frame)
        g12 = _load_frame_field("g12", np.asarray(data["g12"], dtype=np.float64), frame)
        b_k = _load_frame_field(b_key, np.asarray(data[b_key], dtype=np.float64), frame)
    except Exception as exc:
        return None, [f"field_cast:{exc}"], warnings

    if not (lambda2.shape == g12.shape == b_k.shape):
        return None, [
            f"shape_mismatch:{lambda2.shape!r},{g12.shape!r},{b_k.shape!r}"
        ], warnings

    try:
        lambda3, lambda3_source = _choose_lambda3_source(data, lambda2, g12, frame)
    except Exception as exc:
        return None, [f"field_cast_lambda3:{exc}"], warnings

    if not (lambda2.shape == np.asarray(lambda3).shape):
        return None, [
            f"lambda3_shape_mismatch:{lambda2.shape!r},{np.asarray(lambda3).shape!r}"
        ], warnings

    if not np.all(np.isfinite(lambda3)):
        return None, ["nonfinite_lambda3"], warnings
    if not (np.all(np.isfinite(lambda2)) and np.all(np.isfinite(g12)) and np.all(np.isfinite(b_k))):
        return None, ["nonfinite_required_field"], warnings

    pressure_hessian_norm: np.ndarray | None = None
    rho: np.ndarray | None = None
    if "pressure_hessian_norm" in data:
        try:
            pressure_hessian_norm = _load_frame_field(
                "pressure_hessian_norm",
                np.asarray(data["pressure_hessian_norm"], dtype=np.float64),
                frame,
            )
        except Exception as exc:
            return None, [f"field_cast_pressure_hessian_norm:{exc}"], warnings

        if pressure_hessian_norm.shape != lambda2.shape:
            return None, [
                f"pressure_shape_mismatch:{pressure_hessian_norm.shape!r}"
            ], warnings

        if not np.all(np.isfinite(pressure_hessian_norm)):
            return None, ["nonfinite_pressure_hessian_norm"], warnings

        denom = 1.0 + pressure_hessian_norm
        if not np.all(denom > 0.0):
            warnings.append("rho_denominator_nonpositive")
        else:
            rho = b_k / denom

    try:
        grid_spacing_value, _ = _scalar_metadata(data, "grid_spacing")
        domain_length_value, _ = _scalar_metadata(data, "domain_length", "length")
    except Exception as exc:
        return None, [f"scale_metadata:{exc}"], warnings

    grid_spacing = None
    domain_length = None
    scale_source = "index_units"
    n = float(lambda2.shape[0])
    if grid_spacing_value is not None:
        grid_spacing = _finite_float(grid_spacing_value, "grid_spacing")
        if grid_spacing <= 0.0:
            return None, ["grid_spacing_nonpositive"], warnings
        scale_source = "grid_spacing"
        if domain_length_value is not None:
            domain_length = _finite_float(domain_length_value, "domain_length")
            if domain_length <= 0.0:
                return None, ["domain_length_nonpositive"], warnings
            expected = grid_spacing * n
            if not math.isclose(domain_length, expected, rel_tol=1.0e-12, abs_tol=1.0e-12):
                return None, ["grid_spacing_domain_length_mismatch"], warnings
        else:
            domain_length = grid_spacing * n
    elif domain_length_value is not None:
        domain_length = _finite_float(domain_length_value, "domain_length")
        if domain_length <= 0.0:
            return None, ["domain_length_nonpositive"], warnings
        grid_spacing = domain_length / n
        scale_source = "domain_length"
    elif strict:
        return None, ["missing_grid_spacing_or_domain_length"], warnings

    return (
        FieldBundle(
            lambda2=lambda2,
            g12=g12,
            lambda3=np.asarray(lambda3, dtype=np.float64),
            b_k=b_k,
            pressure_hessian_norm=pressure_hessian_norm,
            rho=rho,
            beta=float(beta_value),
            beta_source=beta_source,
            lambda3_source=lambda3_source,
            grid_spacing=None if grid_spacing is None else float(grid_spacing),
            domain_length=None if domain_length is None else float(domain_length),
            scale_source=scale_source,
        ),
        [],
        warnings,
    )


def _label_components(mask: np.ndarray) -> np.ndarray:
    active = np.asarray(mask, dtype=bool)
    if scipy_label is not None and scipy_binary_structure is not None:
        structure = scipy_binary_structure(3, 1)
        labels, _ = scipy_label(active, structure=structure)
        return np.asarray(labels, dtype=np.int32)

    labels = np.zeros(active.shape, dtype=np.int32)
    if not np.any(active):
        return labels

    shape = active.shape
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


def _bbox_and_diameter(mask: np.ndarray) -> tuple[list[int], list[int], int, float | None, float, float]:
    idx = np.argwhere(mask)
    bbox_min = [0, 0, 0]
    bbox_max = [0, 0, 0]
    if idx.size == 0:
        return bbox_min, bbox_max, 0, None, 0.0, 0.0
    mins = np.min(idx, axis=0)
    maxs = np.max(idx, axis=0)
    span = maxs - mins + 1
    bbox_min = [int(v) for v in mins.tolist()]
    bbox_max = [int(v) for v in maxs.tolist()]
    diameter_cells = float(np.max(span))
    return bbox_min, bbox_max, int(np.sum(mask)), float(diameter_cells), int(span[0]), int(span[1])


def _distribution_stats(values: np.ndarray, mask: np.ndarray, quantiles: list[float]) -> dict[str, Any] | None:
    if not np.any(mask):
        return None

    subset = np.asarray(values, dtype=np.float64)[mask]
    if subset.size == 0:
        return None
    if not np.all(np.isfinite(subset)):
        raise ValueError("analysis values contain non-finite entries")

    subset.sort()
    out: dict[str, Any] = {
        "cell_count": int(subset.size),
        "min": float(subset[0]),
        "mean": float(np.mean(subset)),
        "max": float(subset[-1]),
        "sum": float(np.sum(subset)),
    }

    q_vals: list[dict[str, float]] = []
    for q in quantiles:
        q_vals.append({"q": float(q), "value": float(np.quantile(subset, q))})
    out["quantiles"] = q_vals
    return out


def _min_cell_payload(values: np.ndarray, mask: np.ndarray, label: str) -> dict[str, Any] | None:
    if not np.any(mask):
        return None

    subset = np.asarray(values, dtype=np.float64)
    if not np.all(np.isfinite(subset[mask])):
        raise ValueError(f"{label} contains non-finite entries on analysis mask")

    indices = np.argwhere(mask)
    flat_values = subset[mask]
    min_value = float(np.min(flat_values))
    first_min_flat = int(np.flatnonzero(flat_values == min_value)[0])
    min_index = [int(v) for v in indices[first_min_flat].tolist()]
    return {
        "value": min_value,
        "index": min_index,
    }


def _manhattan_distance(a: list[int], b: list[int]) -> int:
    return int(abs(a[0] - b[0]) + abs(a[1] - b[1]) + abs(a[2] - b[2]))


def _select_component(labels: np.ndarray, component_id: int | None, lambda2: np.ndarray, lambda2_band: float) -> tuple[int | None, str | None]:
    component_count = int(labels.max())
    if component_count == 0:
        return None, None

    if component_id is not None:
        if component_id > component_count:
            return None, "requested_component"
        return int(component_id), "requested"

    component_cells = np.bincount(labels.ravel(), minlength=component_count + 1)

    boundary_mask = np.zeros_like(labels, dtype=bool)
    candidate_ids = np.arange(1, component_count + 1, dtype=np.int32)
    boundary_counts = np.zeros_like(candidate_ids, dtype=np.int64)
    for component in candidate_ids:
        boundary_counts[component - 1] = int(np.count_nonzero((labels == component) & (np.abs(lambda2) <= lambda2_band)))

    if boundary_counts.size and np.any(boundary_counts > 0):
        idx = int(np.argmax(boundary_counts))
        return int(candidate_ids[idx]), "largest_boundary_component"

    if component_cells.size > 1:
        idx = int(np.argmax(component_cells[1:]))
        return int(candidate_ids[idx]), "largest_beta_component"
    return None, None


def _relationship_payload(
    min_g12: dict[str, Any] | None,
    min_rho: dict[str, Any] | None,
    component_id: int,
) -> dict[str, Any] | None:
    if min_g12 is None or min_rho is None:
        return None

    g12_idx = min_g12["index"]
    rho_idx = min_rho["index"]
    if not isinstance(g12_idx, list) or not isinstance(rho_idx, list):
        return None

    return {
        "min_g12": {
            "index": g12_idx,
            "value": min_g12["value"],
            "component_id": component_id,
        },
        "min_rho": {
            "index": rho_idx,
            "value": min_rho["value"],
            "component_id": component_id,
        },
        "same_cell": bool(g12_idx == rho_idx),
        "manhattan_distance": _manhattan_distance(g12_idx, rho_idx),
    }


def _render_text(payload: dict[str, Any]) -> str:
    lines = [
        f"status: {payload.get('status')}",
        f"component_id: {payload.get('component_id')}",
        f"component_diameter_cells: {payload.get('component_diameter_cells')}",
        f"boundary_cell_count: {payload.get('boundary_cell_count')}",
        f"tight_band_cell_count: {payload.get('tight_band_cell_count')}",
    ]
    lambda3_stats = payload.get("lambda3_stats")
    if isinstance(lambda3_stats, dict):
        lines.append(f"lambda3_min: {lambda3_stats.get('min')}")
        lines.append(f"lambda3_max: {lambda3_stats.get('max')}")
        lines.append(f"lambda3_mean: {lambda3_stats.get('mean')}")
        lines.append(f"lambda3_sum: {lambda3_stats.get('sum')}")
    if payload.get("lambda3_bounded_away_from_zero") is not None:
        lines.append(f"lambda3_bounded_away_from_zero: {payload.get('lambda3_bounded_away_from_zero')}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for 4D archives")
    parser.add_argument("--component-id", type=_positive_int, default=None, help="target component id; defaults to auto")
    parser.add_argument(
        "--lambda2-band",
        type=float,
        default=DEFAULT_LAMBDA2_BAND,
        help="absolute lambda2 boundary band for diagnostics",
    )
    parser.add_argument(
        "--lambda3-quantiles",
        type=_finite_probability,
        nargs="+",
        default=list(DEFAULT_LAMBDA3_QUANTILES),
        help="quantiles for lambda3 statistics, in [0,1]",
    )
    parser.add_argument(
        "--lambda3-gap-threshold",
        type=_finite_nonnegative_arg,
        default=DEFAULT_DELTA,
        help="delta threshold for bounded-away-from-zero check",
    )
    parser.add_argument("--beta", type=float, default=None, help="override beta threshold")
    parser.add_argument("--strict", action="store_true", help="require physical scale metadata")
    parser.add_argument("--json", action="store_true", help="emit JSON on stdout")
    parser.add_argument("--output", type=Path, default=None, help="optional JSON output path")
    return parser.parse_args()


def _build_payload(args: argparse.Namespace) -> dict[str, Any]:
    if args.lambda2_band < 0.0 or not math.isfinite(args.lambda2_band):
        return {
            "status": STATUS_MISSING,
            "script": SCRIPT_NAME,
            "input": str(args.input),
            "errors": ["invalid_lambda2_band"],
            "authority": _authority(),
            "O": "Emit fail-closed frame/component lambda3 diagnostics from derived NS boundary archives.",
            "R": "Produce bounded-away-from-zero and distribution diagnostics for selected {lambda2 <= beta} components.",
            "C": SCRIPT_NAME,
            "S": "Validate derived NPZ fields, select a beta component (requested or auto), compute boundary/tight layer statistics.",
            "L": "Status is ok only when selected component and analysis layer have finite cells; otherwise fail-closed.",
            "P": ROUTE_DECISION,
            "G": "No theorem or proof promotion is claimed; results are empirical diagnostics.",
            "F": "The run is blocked by invalid inputs when not fail-closed.",
        }

    lambda3_quantiles = sorted(set(float(q) for q in args.lambda3_quantiles))
    if any(not math.isfinite(q) for q in lambda3_quantiles) or any(q < 0.0 or q > 1.0 for q in lambda3_quantiles):
        return {
            "status": STATUS_MISSING,
            "script": SCRIPT_NAME,
            "input": str(args.input),
            "errors": ["invalid_lambda3_quantile"],
            "authority": _authority(),
            "O": "Emit fail-closed frame/component lambda3 diagnostics from derived NS boundary archives.",
            "R": "Produce bounded-away-from-zero and distribution diagnostics for selected {lambda2 <= beta} components.",
            "C": SCRIPT_NAME,
            "S": "Validate derived NPZ fields, select a beta component (requested or auto), compute boundary/tight layer statistics.",
            "L": "Status is ok only when selected component and analysis layer have finite cells; otherwise fail-closed.",
            "P": ROUTE_DECISION,
            "G": "No theorem or proof promotion is claimed; results are empirical diagnostics.",
            "F": "The run is blocked by invalid quantile inputs when not fail-closed.",
        }

    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "producer": PRODUCER_NAME,
        "input": str(args.input),
        "frame": args.frame,
        "lambda2_band": float(args.lambda2_band),
        "lambda3_gap_threshold": float(args.lambda3_gap_threshold),
        "strict": bool(args.strict),
        "lambda3_quantiles": lambda3_quantiles,
        "authority": _authority(),
        "warnings": [],
        "errors": [],
        "O": "Emit fail-closed frame/component lambda3 diagnostics from derived NS boundary archives.",
        "R": "Produce bounded-away-from-zero and distribution diagnostics for selected {lambda2 <= beta} components.",
        "C": SCRIPT_NAME,
        "S": "Validate derived NPZ fields, select a beta component (requested or auto), and compute boundary/tight layer diagnostics.",
        "L": "Status is ok only when selected component and analysis layer have finite cells; otherwise fail-closed.",
        "P": ROUTE_DECISION,
        "G": "No theorem or theorem-analogue promotion is claimed; this is synthetic boundary telemetry.",
        "F": "The run provides empirical telemetry only and does not establish a proof or Clay promotion.",
    }

    bundle, load_errors, load_warnings = _load_fields(
        path=args.input,
        frame=args.frame,
        beta_override=args.beta,
        strict=bool(args.strict),
    )

    if load_warnings:
        payload["warnings"].extend(load_warnings)

    if bundle is None:
        payload["status"] = STATUS_MISSING
        payload["errors"] = sorted(set(load_errors))
        return payload

    bundle_lambda2 = bundle.lambda2
    labels = _label_components(bundle_lambda2 <= bundle.beta)
    component_count = int(labels.max())

    selected_component, component_selector = _select_component(labels, args.component_id, bundle_lambda2, float(args.lambda2_band))
    if selected_component is None:
        payload["status"] = STATUS_COMPONENT_NOT_FOUND
        payload["component_count"] = component_count
        payload["errors"] = ["component_not_found"]
        if args.component_id is not None:
            payload["requested_component_id"] = int(args.component_id)
        payload["component_selector"] = None
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    component_mask = labels == selected_component
    component_cell_count = int(np.count_nonzero(component_mask))
    if component_cell_count <= 0:
        payload["status"] = STATUS_COMPONENT_NOT_FOUND
        payload["component_count"] = component_count
        payload["requested_component_id"] = int(args.component_id) if args.component_id is not None else None
        payload["component_selector"] = component_selector
        payload["errors"] = ["component_empty"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    bbox_min, bbox_max, _tmp_count, diameter_cells, _, _ = _bbox_and_diameter(component_mask)
    component_diameter_cells = diameter_cells
    component_diameter_physical = None if bundle.grid_spacing is None else float(diameter_cells * bundle.grid_spacing)

    tight_mask = component_mask & (bundle_lambda2 <= bundle.beta)
    tight_count = int(np.count_nonzero(tight_mask))
    boundary_mask = component_mask & (np.abs(bundle_lambda2) <= float(args.lambda2_band))
    boundary_count = int(np.count_nonzero(boundary_mask))

    if boundary_count > 0:
        analysis_mask = boundary_mask
        analysis_source = "boundary_abs_lambda2"
    else:
        analysis_mask = tight_mask
        analysis_source = "tight_lambda2_beta"
        payload["warnings"].append("boundary_mask_empty_fallback_to_tight_band")

    if not np.any(analysis_mask):
        payload["status"] = STATUS_NO_ANALYSIS_CELLS
        payload["component_count"] = component_count
        payload["component_id"] = int(selected_component)
        payload["component_selector"] = component_selector
        payload["component_cell_count"] = component_cell_count
        payload["component_diameter_cells"] = component_diameter_cells
        payload["component_diameter_physical"] = component_diameter_physical
        payload["boundary_cell_count"] = boundary_count
        payload["tight_band_cell_count"] = tight_count
        payload["errors"] = ["analysis_mask_empty"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    boundary_stats = _distribution_stats(bundle.lambda3, boundary_mask, lambda3_quantiles)
    tight_stats = _distribution_stats(bundle.lambda3, tight_mask, lambda3_quantiles)
    analysis_stats = _distribution_stats(bundle.lambda3, analysis_mask, lambda3_quantiles)
    if analysis_stats is None:
        payload["status"] = STATUS_NO_ANALYSIS_CELLS
        payload["errors"] = ["analysis_values_empty_after_mask"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    lambda3_analysis_values = np.asarray(bundle.lambda3, dtype=np.float64)[analysis_mask]
    lambda3_min_abs = float(np.min(np.abs(lambda3_analysis_values)))
    lambda3_bounded_away_from_zero = bool(lambda3_min_abs > float(args.lambda3_gap_threshold))

    min_g12 = _min_cell_payload(bundle.g12, analysis_mask, "g12")
    min_rho = None
    if bundle.rho is not None:
        try:
            min_rho = _min_cell_payload(bundle.rho, analysis_mask, "rho")
        except ValueError:
            min_rho = None
            payload["warnings"].append("rho_invalid_on_analysis_mask")

    relationship = _relationship_payload(min_g12, min_rho, int(selected_component))

    payload.update(
        {
            "status": OK_STATUS,
            "component_count": component_count,
            "component_id": int(selected_component),
            "component_selector": component_selector,
            "requested_component_id": int(args.component_id) if args.component_id is not None else None,
            "shape": [int(v) for v in bundle_lambda2.shape],
            "grid_spacing": None if bundle.grid_spacing is None else float(bundle.grid_spacing),
            "domain_length": None if bundle.domain_length is None else float(bundle.domain_length),
            "scale_source": bundle.scale_source,
            "beta": float(bundle.beta),
            "beta_source": bundle.beta_source,
            "lambda3_source": bundle.lambda3_source,
            "component_cell_count": component_cell_count,
            "component_diameter_cells": float(component_diameter_cells),
            "component_diameter_physical": component_diameter_physical,
            "component_bbox_min": bbox_min,
            "component_bbox_max": bbox_max,
            "analysis_mask_source": analysis_source,
            "boundary_cell_count": boundary_count,
            "tight_band_cell_count": tight_count,
            "lambda3_stats": analysis_stats,
            "boundary_lambda3_stats": boundary_stats,
            "tight_band_lambda3_stats": tight_stats,
            "lambda3_min_abs": lambda3_min_abs,
            "lambda3_bounded_away_from_zero": lambda3_bounded_away_from_zero,
            "min_g12": min_g12,
            "min_g12_value": None if min_g12 is None else float(min_g12["value"]),
            "min_rho": min_rho,
            "min_rho_value": None if min_rho is None else float(min_rho["value"]),
            "min_g12_min_rho_relationship": relationship,
        }
    )

    if relationship is None:
        payload["warnings"].append("min_g12_min_rho_relationship_unavailable")
    elif relationship.get("same_cell"):
        payload["warnings"].append("min_g12_cell_and_min_rho_cell_are_same")

    payload["errors"] = []
    payload["warnings"] = sorted(set(str(w) for w in payload["warnings"]))
    return payload


def main() -> int:
    args = parse_args()
    payload = _build_payload(args)
    text = _json_text(payload)

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")

    if args.json:
        print(text)
    else:
        print(_render_text(payload))

    return 0 if payload.get("status") == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
