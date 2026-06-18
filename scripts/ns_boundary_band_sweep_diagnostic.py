#!/usr/bin/env python3
"""Calc 10 boundary-band sweep for NS Korn diagnostics.

This runner consumes a derived tensor archive and sweeps several ``|lambda2|``
boundary bands for one component. It is empirical and fail-closed: it reports
candidate-only ratios for the Korn denominator and the strain/rotation split,
but it does not promote ``KornLevelSet`` or any Clay theorem claim.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import scripts.ns_boundary_korn_ratio_diagnostic as korn_diag
import scripts.ns_boundary_layer_thickness_diagnostic as thickness_diag
from scripts.ns_boundary_layer_thickness_diagnostic import _label_components


SCRIPT_NAME = "scripts/ns_boundary_band_sweep_diagnostic.py"
CONTRACT = "ns_boundary_band_sweep_diagnostic"
OK_STATUS = "ok"
DEFAULT_LAYER_RADIUS_CELLS = 2
TRUE_DENOMINATOR_FIELDS = ("velocity_hessian_norm_squared", "u_hessian_norm_squared")
STRAIN_FIELD = "strain_hessian_norm_squared"
ANTISYM_FIELDS = ("antisym_hessian_norm_squared", "vorticity_hessian_norm_squared")


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


def _finite_nonnegative_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError("value must be finite and nonnegative")
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


def _squeeze_field(name: str, value: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(value, dtype=np.float64)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) != 1:
                raise ValueError(f"{name} is multi-frame; pass --frame")
            arr = arr[0]
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"frame {frame} is out of range for {name} with {arr.shape[0]} frame(s)")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be 3D or 4D, got {arr.shape!r}")
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} contains non-finite values")
    return arr


def _load_named_field(path: Path, names: tuple[str, ...], frame: int | None) -> tuple[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        for name in names:
            if name in data:
                return name, _squeeze_field(name, np.asarray(data[name]), frame)
    raise KeyError(f"missing required field; expected one of {list(names)!r}")


def _load_optional_scalar(path: Path, names: tuple[str, ...], default: float) -> float:
    with np.load(path, allow_pickle=False) as data:
        for name in names:
            if name not in data:
                continue
            value = np.asarray(data[name])
            if value.shape == ():
                return float(value.item())
            if value.ndim == 1 and value.size == 1:
                return float(value[0])
            raise ValueError(f"{name} must be scalar for Calc 10, got {value.shape!r}")
    return float(default)


def _load_optional_named_field(path: Path, names: tuple[str, ...], frame: int | None) -> tuple[str | None, np.ndarray | None]:
    try:
        return _load_named_field(path, names, frame)
    except KeyError:
        return None, None


def _load_component_labels(path: Path, frame: int | None, lambda2: np.ndarray, beta: float) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        for name in ("component_labels", "labels", "component_label"):
            if name in data:
                labels = np.asarray(data[name])
                if labels.ndim == 4:
                    if frame is None:
                        if int(labels.shape[0]) != 1:
                            raise ValueError(f"{name} is multi-frame; pass --frame")
                        labels = labels[0]
                    else:
                        labels = labels[frame]
                if labels.shape != lambda2.shape:
                    raise ValueError(f"{name} shape {labels.shape!r} does not match lambda2 {lambda2.shape!r}")
                return np.asarray(labels, dtype=np.int64)
    return _label_components(lambda2 <= beta)


def _rho_field(path: Path, b_k: np.ndarray, pressure_hessian_norm: np.ndarray, frame: int | None) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        if "rho" in data:
            rho = _squeeze_field("rho", np.asarray(data["rho"]), frame)
            if rho.shape != b_k.shape:
                raise ValueError("rho shape does not match B_k shape")
            return rho
    return b_k / (1.0 + pressure_hessian_norm)


def _load_rho_or_pressure(path: Path, b_k: np.ndarray, frame: int | None) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        if "rho" in data:
            rho = _squeeze_field("rho", np.asarray(data["rho"]), frame)
            if rho.shape != b_k.shape:
                raise ValueError("rho shape does not match B_k shape")
            return rho
    _, pressure_hessian_norm = _load_named_field(path, ("pressure_hessian_norm",), frame)
    return _rho_field(path, b_k, pressure_hessian_norm, frame)


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


def _scale_metadata(path: Path) -> tuple[float | None, float | None]:
    with np.load(path, allow_pickle=False) as data:
        grid_spacing = None
        domain_length = None
        if "grid_spacing" in data and np.asarray(data["grid_spacing"]).shape == ():
            grid_spacing = float(np.asarray(data["grid_spacing"]).item())
        if "domain_length" in data and np.asarray(data["domain_length"]).shape == ():
            domain_length = float(np.asarray(data["domain_length"]).item())
    return grid_spacing, domain_length


def _layer_thickness_stats(
    *,
    lambda2: np.ndarray,
    labels: np.ndarray,
    component_id: int,
    band: float,
    spacing: float | None,
    beta: float,
) -> tuple[float | None, float | None]:
    grad_x, grad_y, grad_z, grad_mag = thickness_diag._gradient_components(lambda2, spacing)
    summary = thickness_diag._component_summary(
        component_id=int(component_id),
        labels=labels,
        lambda2=lambda2,
        grad_mag=grad_mag,
        grad_vec=(grad_x, grad_y, grad_z),
        layer_mask=np.asarray(np.abs(lambda2) <= float(band), dtype=bool),
        beta=beta,
        radius=thickness_diag.DEFAULT_MAX_SEARCH_RADIUS_CELLS,
        spacing=spacing,
    )
    thickness_stats = summary.get("thickness_stats")
    if not isinstance(thickness_stats, dict):
        return None, None
    return (
        None if thickness_stats.get("transition_thickness_cells_mean") is None else float(thickness_stats["transition_thickness_cells_mean"]),
        None
        if thickness_stats.get("transition_thickness_physical_mean") is None
        else float(thickness_stats["transition_thickness_physical_mean"]),
    )


def _row(
    *,
    path: Path,
    frame: int | None,
    component_id: int,
    band: float,
    layer_radius_cells: int,
    strict: bool,
    allow_missing_alpha: bool,
    layer_thickness_override_physical: float | None,
) -> dict[str, Any]:
    _, lambda2 = _load_named_field(path, ("lambda2",), frame)
    _, g12 = _load_named_field(path, ("g12",), frame)
    _, b_k = _load_named_field(path, ("B_k", "B_k_max"), frame)
    beta = _load_optional_scalar(path, ("beta",), 0.0)
    grid_spacing, domain_length = _scale_metadata(path)

    labels = _load_component_labels(path, frame, lambda2, beta)
    component_count = int(labels.max())
    if component_id > component_count or not np.any(labels == component_id):
        return {"status": "component_not_found", "band": band, "lambda2_band": band, "component_count": component_count}

    true_name, true_denominator = _load_named_field(path, TRUE_DENOMINATOR_FIELDS, frame)
    strain_name, strain_denominator = _load_optional_named_field(path, (STRAIN_FIELD,), frame)
    antisym_name, antisym_denominator = _load_optional_named_field(path, ANTISYM_FIELDS, frame)
    if (strain_denominator is None or antisym_denominator is None) and not allow_missing_alpha:
        return {
            "status": "missing_required_field",
            "band": band,
            "lambda2_band": band,
            "errors": [
                name
                for name, field in (
                    (STRAIN_FIELD, strain_denominator),
                    ("/".join(ANTISYM_FIELDS), antisym_denominator),
                )
                if field is None
            ],
        }
    for name, field in (
        (true_name, true_denominator),
        (strain_name, strain_denominator),
        (antisym_name, antisym_denominator),
    ):
        if field is None:
            continue
        if field.shape != lambda2.shape:
            raise ValueError(f"{name} shape {field.shape!r} does not match lambda2 {lambda2.shape!r}")
        if np.any(field < -1.0e-9):
            raise ValueError(f"{name} contains negative values")

    component_mask = labels == component_id
    boundary_mask = component_mask & (np.abs(lambda2) <= band)
    if not np.any(boundary_mask):
        return {"status": "no_boundary_cells", "band": band, "lambda2_band": band, "component_count": component_count}

    spacing = grid_spacing
    effective_layer_radius = layer_radius_cells
    if layer_thickness_override_physical is not None:
        if spacing is None:
            return {
                "status": "missing_required_field",
                "band": band,
                "lambda2_band": band,
                "errors": ["layer_thickness_physical_requires_grid_spacing"],
            }
        effective_layer_radius = max(1, int(math.ceil(float(layer_thickness_override_physical) / float(spacing))))
    layer_mask = korn_diag._dilate(boundary_mask, effective_layer_radius) & component_mask
    if not np.any(layer_mask):
        return {"status": "no_layer_cells", "band": band, "lambda2_band": band}

    area_scale = 1.0 if spacing is None else float(spacing) ** 2
    volume_scale = 1.0 if spacing is None else float(spacing) ** 3
    rho = _load_rho_or_pressure(path, b_k, frame)

    numerator = float(np.sum(b_k[boundary_mask]) * area_scale)
    true_integral = float(np.sum(true_denominator[layer_mask]) * volume_scale)
    if true_integral <= 0.0:
        return {
            "status": "no_layer_cells",
            "band": band,
            "lambda2_band": band,
            "errors": ["nonpositive_true_denominator"],
        }
    strain_integral = None if strain_denominator is None else float(np.sum(strain_denominator[layer_mask]) * volume_scale)
    omega_integral = None if antisym_denominator is None else float(np.sum(antisym_denominator[layer_mask]) * volume_scale)
    alpha_strain_sq = None if strain_integral is None else float(strain_integral / true_integral)
    alpha_omega_sq = None if omega_integral is None else float(omega_integral / true_integral)

    layer_thickness_cells, layer_thickness_physical = _layer_thickness_stats(
        lambda2=lambda2,
        labels=labels,
        component_id=component_id,
        band=band,
        spacing=spacing,
        beta=beta,
    )

    row: dict[str, Any] = {
        "status": OK_STATUS,
        "band": float(band),
        "lambda2_band": float(band),
        "component_id": int(component_id),
        "component_count": component_count,
        "component_cell_count": int(np.count_nonzero(component_mask)),
        "boundary_cell_count": int(np.count_nonzero(boundary_mask)),
        "boundary_mask_source": "component_absolute_lambda2_band",
        "layer_cell_count": int(np.count_nonzero(layer_mask)),
        "layer_radius_cells": int(effective_layer_radius),
        "layer_radius_physical": None if spacing is None else float(effective_layer_radius * float(spacing)),
        "layer_thickness_cells": layer_thickness_cells,
        "layer_thickness_physical": layer_thickness_physical,
        "layer_thickness_override_physical": None
        if layer_thickness_override_physical is None
        else float(layer_thickness_override_physical),
        "grid_spacing": None if spacing is None else float(spacing),
        "domain_length": None if domain_length is None else float(domain_length),
        "scale_source": "grid_spacing" if spacing is not None else "unit",
        "beta": float(beta),
        "beta_source": "archive" if _load_optional_scalar(path, ("beta",), math.nan) == beta else "default-zero",
        "denominator_kind": str(true_name),
        "strain_denominator_kind": None if strain_name is None else str(strain_name),
        "antisym_denominator_kind": None if antisym_name is None else str(antisym_name),
        "numerator_int_boundary_Bk_dH2": numerator,
        "denominator_int_layer_velocity_hessian_norm_squared_dx": true_integral,
        "denominator_int_layer_strain_dx": None if strain_integral is None else float(strain_integral),
        "denominator_int_layer_antisym_dx": None if omega_integral is None else float(omega_integral),
        "c_empirical_true": float(numerator / true_integral),
        "alpha_strain_sq": alpha_strain_sq,
        "alpha_omega_sq": alpha_omega_sq,
        "min_g12": float(np.min(g12[boundary_mask])),
        "rho_min": float(np.min(rho[boundary_mask])),
        "rho_mean": float(np.mean(rho[boundary_mask])),
        "boundary_Bk_stats": _stats(b_k[boundary_mask]),
        "boundary_g12_stats": _stats(g12[boundary_mask]),
        "boundary_rho_stats": _stats(rho[boundary_mask]),
        "layer_true_denominator_stats": _stats(true_denominator[layer_mask]),
        "layer_strain_denominator_stats": None if strain_denominator is None else _stats(strain_denominator[layer_mask]),
        "layer_antisym_denominator_stats": None if antisym_denominator is None else _stats(antisym_denominator[layer_mask]),
        "warnings": [],
        "errors": [],
        "authority": _authority(),
        "notes": [
            "result is empirical and non-promoting; it is not an analytic KornLevelSet proof",
            "alpha_strain_sq and alpha_omega_sq are layer integrals divided by velocity_hessian_norm_squared",
        ],
    }
    if strain_denominator is None:
        row["warnings"].append("strain_alpha_missing")
    if antisym_denominator is None:
        row["warnings"].append("omega_alpha_missing")
    row["warnings"] = sorted(set(row["warnings"]))
    return row


def _summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def finite(name: str) -> list[float]:
        out: list[float] = []
        for row in ok_rows:
            value = row.get(name)
            if value is None:
                continue
            number = float(value)
            if math.isfinite(number):
                out.append(number)
        return out

    c_true = finite("c_empirical_true")
    alpha_strain = finite("alpha_strain_sq")
    alpha_omega = finite("alpha_omega_sq")
    min_g12 = finite("min_g12")
    rho_min = finite("rho_min")
    layer_thickness = finite("layer_thickness_physical")
    return {
        "ok_row_count": len(ok_rows),
        "processed_band_count": len(rows),
        "status_counts": {
            status: sum(1 for row in rows if str(row.get("status")) == status)
            for status in sorted({str(row.get("status", "missing_required_field")) for row in rows})
        },
        "c_empirical_true_min": None if not c_true else min(c_true),
        "c_empirical_true_mean": None if not c_true else float(sum(c_true) / len(c_true)),
        "c_empirical_true_max": None if not c_true else max(c_true),
        "alpha_strain_sq_min": None if not alpha_strain else min(alpha_strain),
        "alpha_strain_sq_mean": None if not alpha_strain else float(sum(alpha_strain) / len(alpha_strain)),
        "alpha_strain_sq_max": None if not alpha_strain else max(alpha_strain),
        "alpha_omega_sq_min": None if not alpha_omega else min(alpha_omega),
        "alpha_omega_sq_mean": None if not alpha_omega else float(sum(alpha_omega) / len(alpha_omega)),
        "alpha_omega_sq_max": None if not alpha_omega else max(alpha_omega),
        "layer_thickness_physical_min": None if not layer_thickness else min(layer_thickness),
        "layer_thickness_physical_mean": None if not layer_thickness else float(sum(layer_thickness) / len(layer_thickness)),
        "layer_thickness_physical_max": None if not layer_thickness else max(layer_thickness),
        "min_g12_min": None if not min_g12 else min(min_g12),
        "rho_min_min": None if not rho_min else min(rho_min),
        "true_ratio_bounded_away_from_zero_empirical": bool(c_true and min(c_true) > 0.0),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="derived tensor NPZ archive")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for 4D archives")
    parser.add_argument("--component-id", type=_positive_int, required=True)
    parser.add_argument("--bands", nargs="+", type=_finite_nonnegative_float, required=True)
    parser.add_argument("--layer-radius-cells", type=_positive_int, default=DEFAULT_LAYER_RADIUS_CELLS)
    parser.add_argument("--layer-thickness-physical", type=_finite_nonnegative_float, default=None)
    parser.add_argument("--allow-missing-alpha", action="store_true")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "input": str(args.input),
        "frame": args.frame,
        "component_id": int(args.component_id),
        "bands": [float(value) for value in args.bands],
        "strict": bool(args.strict),
        "allow_missing_alpha": bool(args.allow_missing_alpha),
        "rows": [],
        "authority": _authority(),
        "warnings": [],
        "errors": [],
    }

    try:
        rows = [
            _row(
                path=args.input,
                frame=args.frame,
                component_id=int(args.component_id),
                band=float(band),
                layer_radius_cells=int(args.layer_radius_cells),
                strict=bool(args.strict),
                allow_missing_alpha=bool(args.allow_missing_alpha),
                layer_thickness_override_physical=args.layer_thickness_physical,
            )
            for band in args.bands
        ]
        payload["rows"] = rows
        payload["summary"] = _summary(rows)
        payload["warnings"] = sorted(
            {
                warning
                for row in rows
                for warning in row.get("warnings", [])
                if isinstance(warning, str)
            }
        )
        statuses = [str(row.get("status", "missing_required_field")) for row in rows]
        if rows and all(status == OK_STATUS for status in statuses):
            payload["status"] = OK_STATUS
        elif rows and len(set(statuses)) == 1:
            payload["status"] = statuses[0]
        else:
            payload["status"] = "partial"
        payload["errors"] = sorted({status for status in statuses if status != OK_STATUS})
    except Exception as exc:
        payload["status"] = "missing_required_field"
        payload["errors"] = [f"{type(exc).__name__}:{exc}"]
        payload["summary"] = _summary([])

    text = _json_text(payload)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print(f"status: {payload.get('status')}")
        print(f"rows: {len(payload.get('rows', []))}")
        print(f"summary: {payload.get('summary', {})}")
    return 0 if payload.get("status") == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
