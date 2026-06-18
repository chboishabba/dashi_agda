#!/usr/bin/env python3
"""Calc 6 empirical Korn-level-set proxy diagnostic for NS boundary archives.

This diagnostic consumes a derived tensor archive produced by
``scripts/ns_boundary_derived_tensor_archive.py`` and estimates the component
ratio

    int_{partial C} max_k B_k dH^2 / int_{layer_delta(C)} proxy dx.

The current derived archive does not materialize ``|nabla^2 u|^2``.  Therefore
the default denominator is an explicit proxy,
``|nabla lambda2|^2``.  The JSON payload records ``denominator_kind`` so the
result cannot be confused with an analytic Korn constant.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_layer_thickness_diagnostic import (
    _gradient_components,
    _label_components,
    _load_fields,
)


SCRIPT_NAME = "scripts/ns_boundary_korn_ratio_diagnostic.py"
CONTRACT = "ns_boundary_korn_ratio_diagnostic"
DEFAULT_LAMBDA2_BAND = 1.0e-3
DEFAULT_LAYER_RADIUS_CELLS = 2
OK_STATUS = "ok"

try:  # Optional dependency.
    from scipy.ndimage import binary_dilation as scipy_binary_dilation
    from scipy.ndimage import generate_binary_structure as scipy_binary_structure
except Exception:  # pragma: no cover - optional dependency.
    scipy_binary_dilation = None
    scipy_binary_structure = None


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def _finite_nonnegative_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError("value must be finite and nonnegative")
    return parsed


def _stats(values: np.ndarray) -> dict[str, float | None]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"min": None, "mean": None, "max": None, "sum": None}
    return {
        "min": float(np.min(arr)),
        "mean": float(np.mean(arr)),
        "max": float(np.max(arr)),
        "sum": float(np.sum(arr)),
    }


def _dilate(mask: np.ndarray, radius_cells: int) -> np.ndarray:
    active = np.asarray(mask, dtype=bool)
    if radius_cells <= 0:
        return active.copy()
    if scipy_binary_dilation is not None and scipy_binary_structure is not None:
        structure = scipy_binary_structure(3, 1)
        return np.asarray(scipy_binary_dilation(active, structure=structure, iterations=radius_cells), dtype=bool)

    out = active.copy()
    shape = active.shape
    frontier = active.copy()
    for _ in range(radius_cells):
        expanded = out.copy()
        coords = np.argwhere(frontier)
        for x, y, z in coords:
            for nx, ny, nz in (
                (x - 1, y, z),
                (x + 1, y, z),
                (x, y - 1, z),
                (x, y + 1, z),
                (x, y, z - 1),
                (x, y, z + 1),
            ):
                if nx < 0 or ny < 0 or nz < 0:
                    continue
                if nx >= shape[0] or ny >= shape[1] or nz >= shape[2]:
                    continue
                expanded[nx, ny, nz] = True
        frontier = expanded & ~out
        out = expanded
    return out


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--component-id", type=_positive_int, required=True, help="target component id")
    parser.add_argument("--lambda2-band", type=_finite_nonnegative_float, default=DEFAULT_LAMBDA2_BAND)
    parser.add_argument("--beta", type=float, default=None, help="override beta threshold")
    parser.add_argument("--layer-radius-cells", type=_positive_int, default=DEFAULT_LAYER_RADIUS_CELLS)
    parser.add_argument(
        "--layer-thickness-physical",
        type=_finite_nonnegative_float,
        default=None,
        help="override layer radius in physical units; converted to grid cells by ceiling",
    )
    parser.add_argument("--strict", action="store_true", help="require scale metadata")
    parser.add_argument("--json", action="store_true", help="emit JSON on stdout")
    parser.add_argument("--output", type=Path, default=None, help="optional JSON output path")
    return parser.parse_args()


def _json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _component_payload(args: argparse.Namespace) -> dict[str, Any]:
    bundle, missing = _load_fields(args.input, args.beta, args.strict)
    base: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "input": str(args.input),
        "status": OK_STATUS,
        "strict": bool(args.strict),
        "component_id": int(args.component_id),
        "lambda2_band": float(args.lambda2_band),
        "requested_layer_radius_cells": int(args.layer_radius_cells),
        "layer_thickness_physical": None if args.layer_thickness_physical is None else float(args.layer_thickness_physical),
        "denominator_kind": "grad_lambda2_squared_proxy",
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
    }
    if bundle is None:
        base.update({"status": "missing_required_field", "errors": sorted(set(missing))})
        return base

    lambda2 = bundle.lambda2
    labels = _label_components(lambda2 <= bundle.beta)
    component_count = int(labels.max())
    if args.component_id > component_count or not np.any(labels == args.component_id):
        base.update({"status": "component_not_found", "component_count": component_count})
        return base

    spacing = bundle.grid_spacing
    if args.layer_thickness_physical is not None:
        if spacing is None:
            base.update({"status": "missing_required_field", "errors": ["layer_thickness_physical_requires_grid_spacing"]})
            return base
        layer_radius_cells = max(1, int(math.ceil(float(args.layer_thickness_physical) / float(spacing))))
    else:
        layer_radius_cells = int(args.layer_radius_cells)

    component_mask = labels == args.component_id
    boundary_mask = component_mask & (np.abs(lambda2) <= float(args.lambda2_band))
    boundary_mask_source = "component_absolute_lambda2_band"
    if not np.any(boundary_mask):
        boundary_mask = component_mask & (lambda2 <= bundle.beta)
        boundary_mask_source = "component_beta_sublevel_fallback"
    if not np.any(boundary_mask):
        base.update({"status": "no_boundary_cells", "component_count": component_count})
        return base

    layer_mask = _dilate(boundary_mask, layer_radius_cells)
    layer_mask &= component_mask
    if not np.any(layer_mask):
        base.update({"status": "no_layer_cells", "component_count": component_count})
        return base

    _, _, _, grad_mag = _gradient_components(lambda2, spacing)
    area_scale = 1.0 if spacing is None else float(spacing) ** 2
    volume_scale = 1.0 if spacing is None else float(spacing) ** 3
    numerator_density = bundle.b_k[boundary_mask]
    denominator_density = grad_mag[layer_mask] ** 2
    numerator = float(np.sum(numerator_density) * area_scale)
    denominator = float(np.sum(denominator_density) * volume_scale)
    ratio = None if denominator <= 0.0 else float(numerator / denominator)
    rho = bundle.b_k / (1.0 + bundle.pressure_hessian_norm)

    base.update(
        {
            "status": OK_STATUS,
            "shape": [int(v) for v in lambda2.shape],
            "beta": float(bundle.beta),
            "beta_source": bundle.beta_source,
            "grid_spacing": None if spacing is None else float(spacing),
            "domain_length": None if bundle.domain_length is None else float(bundle.domain_length),
            "scale_source": bundle.scale_source,
            "component_count": component_count,
            "component_cell_count": int(np.count_nonzero(component_mask)),
            "boundary_cell_count": int(np.count_nonzero(boundary_mask)),
            "layer_cell_count": int(np.count_nonzero(layer_mask)),
            "boundary_mask_source": boundary_mask_source,
            "layer_radius_cells": int(layer_radius_cells),
            "layer_radius_physical": None if spacing is None else float(layer_radius_cells * float(spacing)),
            "surface_area_cell_scale": float(area_scale),
            "volume_cell_scale": float(volume_scale),
            "numerator_int_boundary_Bk_dH2": numerator,
            "denominator_int_layer_grad_lambda2_squared_dx": denominator,
            "c_empirical_proxy": ratio,
            "boundary_Bk_stats": _stats(numerator_density),
            "layer_grad_lambda2_squared_stats": _stats(denominator_density),
            "boundary_g12_stats": _stats(bundle.g12[boundary_mask]),
            "boundary_rho_stats": _stats(rho[boundary_mask]),
            "boundary_grad_lambda2_stats": _stats(grad_mag[boundary_mask]),
            "notes": [
                "denominator is |grad lambda2|^2 proxy because derived archive does not materialize |nabla^2 u|^2",
                "result is empirical and non-promoting; it is not an analytic KornLevelSet proof",
            ],
        }
    )
    return base


def _render_text(payload: dict[str, Any]) -> str:
    return "\n".join(
        [
            f"status: {payload.get('status')}",
            f"component_id: {payload.get('component_id')}",
            f"boundary_cell_count: {payload.get('boundary_cell_count')}",
            f"layer_cell_count: {payload.get('layer_cell_count')}",
            f"denominator_kind: {payload.get('denominator_kind')}",
            f"c_empirical_proxy: {payload.get('c_empirical_proxy')}",
        ]
    )


def main() -> int:
    args = parse_args()
    payload = _component_payload(args)
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
