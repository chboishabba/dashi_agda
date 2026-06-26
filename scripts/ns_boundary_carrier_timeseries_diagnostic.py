#!/usr/bin/env python3
"""Calc 7 temporal persistence diagnostic for NS boundary carrier components.

The script consumes either:

* one derived ``.npz`` archive with a leading snapshot axis on the tensor
  fields, or
* a directory of per-frame derived ``.npz`` archives.

For each frame it reuses the existing boundary component diagnostic to locate
the carrier-adjacent component around the minimum-rho / minimum-g12 boundary
geometry, then reuses the layer-thickness diagnostic to measure the carrier
layer thickness when possible.

The output is a compact per-frame record with carrier identity, boundary
sample counts, component size, gradient statistics, and the minimum g12 / rho
metrics needed by the temporal persistence lane.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import sys
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import scripts.ns_boundary_component_diagnostic as component_diag
import scripts.ns_boundary_layer_thickness_diagnostic as thickness_diag

SCRIPT_NAME = "scripts/ns_boundary_carrier_timeseries_diagnostic.py"
CONTRACT = "ns_boundary_carrier_timeseries_diagnostic"
DEFAULT_LAMBDA2_BAND = 1.0e-3
DEFAULT_LAYER_SEARCH_RADIUS_CELLS = int(thickness_diag.DEFAULT_MAX_SEARCH_RADIUS_CELLS)


@dataclass(frozen=True)
class FrameSource:
    source_path: Path
    label: str
    frame_index: int | None
    frame_count: int
    data: dict[str, np.ndarray]


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def _finite_float(value: Any, name: str) -> float:
    scalar = float(value)
    if not math.isfinite(scalar):
        raise ValueError(f"{name} must be finite")
    return scalar


def _json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    return component_diag._load_npz(path)


def _required_field_name(data: dict[str, np.ndarray]) -> str:
    if "B_k" in data:
        return "B_k"
    if "B_k_max" in data:
        return "B_k_max"
    return "B_k"


def _true_denominator_kind(data: dict[str, np.ndarray]) -> str | None:
    if "velocity_hessian_norm_squared" in data:
        return "velocity_hessian_norm_squared"
    return None


def _frame_axis_count(data: dict[str, np.ndarray]) -> int:
    frame_counts: set[int] = set()
    saw_3d = False
    for name in ("lambda2", "g12", "B_k", "B_k_max", "pressure_hessian_norm"):
        if name not in data:
            continue
        array = np.asarray(data[name])
        if array.ndim == 4:
            frame_counts.add(int(array.shape[0]))
        elif array.ndim == 3:
            saw_3d = True
        elif array.ndim != 3:
            raise ValueError(f"{name} must be 3D or 4D, got shape {array.shape!r}")
    if not frame_counts:
        if saw_3d:
            return 1
        raise ValueError("input archive is missing required 3D/4D tensor fields")
    if len(frame_counts) != 1:
        raise ValueError(f"tensor frame counts do not match: {sorted(frame_counts)!r}")
    if saw_3d:
        raise ValueError("mixed 3D and 4D tensor fields are not supported in a single archive")
    return frame_counts.pop()


def _slice_frame(array: np.ndarray, frame_index: int, frame_count: int, label: str) -> np.ndarray:
    value = np.asarray(array)
    if value.ndim == 3:
        return value
    if value.ndim == 4:
        if int(value.shape[0]) != frame_count:
            raise ValueError(f"{label} frame count {value.shape[0]} does not match the archive frame count {frame_count}")
        return np.asarray(value[frame_index])
    if value.ndim == 0:
        return value
    if value.ndim == 1 and int(value.shape[0]) == frame_count:
        return np.asarray(value[frame_index])
    raise ValueError(f"{label} must be scalar, 1D per-frame, or 3D/4D tensor data; got {value.shape!r}")


def _scalar_frame_value(
    data: dict[str, np.ndarray],
    names: tuple[str, ...],
    frame_index: int | None,
    frame_count: int,
) -> tuple[float | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape == ():
            scalar = value.item()
            if isinstance(scalar, np.generic):
                scalar = scalar.item()
            return _finite_float(scalar, name), name
        if value.ndim == 1 and int(value.shape[0]) == frame_count:
            if frame_index is None:
                if frame_count != 1:
                    raise ValueError(f"{name} is per-frame metadata but the archive has {frame_count} frames")
                scalar = value[0]
            else:
                scalar = value[frame_index]
            if isinstance(scalar, np.generic):
                scalar = scalar.item()
            return _finite_float(scalar, name), name
        raise ValueError(f"{name} metadata must be scalar or 1D with one entry per frame, got {value.shape!r}")
    return None, None


def _optional_frame_bundle(data: dict[str, np.ndarray], frame_index: int | None, frame_count: int) -> tuple[thickness_diag.FieldBundle, list[str]]:
    warnings: list[str] = []
    b_key = _required_field_name(data)
    required_keys = ("lambda2", "g12", b_key, "pressure_hessian_norm")
    missing = [key for key in required_keys if key not in data]
    if missing:
        raise ValueError(f"missing required keys: {missing!r}")

    lambda2 = _slice_frame(np.asarray(data["lambda2"], dtype=np.float64), 0 if frame_index is None else frame_index, frame_count, "lambda2")
    g12 = _slice_frame(np.asarray(data["g12"], dtype=np.float64), 0 if frame_index is None else frame_index, frame_count, "g12")
    b_k = _slice_frame(np.asarray(data[b_key], dtype=np.float64), 0 if frame_index is None else frame_index, frame_count, b_key)
    pressure_hessian_norm = _slice_frame(
        np.asarray(data["pressure_hessian_norm"], dtype=np.float64),
        0 if frame_index is None else frame_index,
        frame_count,
        "pressure_hessian_norm",
    )

    if not (lambda2.shape == g12.shape == b_k.shape == pressure_hessian_norm.shape):
        raise ValueError(
            "shape mismatch: "
            f"lambda2={lambda2.shape!r}, g12={g12.shape!r}, "
            f"{b_key}={b_k.shape!r}, pressure_hessian_norm={pressure_hessian_norm.shape!r}"
        )
    if lambda2.ndim != 3:
        raise ValueError(f"supported frame layout is 3D per frame; got {lambda2.shape!r}")
    if not (
        np.all(np.isfinite(lambda2))
        and np.all(np.isfinite(g12))
        and np.all(np.isfinite(b_k))
        and np.all(np.isfinite(pressure_hessian_norm))
    ):
        raise ValueError("required tensor fields must be finite")

    beta_value, beta_source = _scalar_frame_value(data, ("beta",), frame_index, frame_count)
    if beta_value is None:
        beta_value = 0.0
        beta_source = "default_zero"
        warnings.append("beta_missing_defaulted_to_zero")

    grid_spacing_value, _ = _scalar_frame_value(data, ("grid_spacing",), frame_index, frame_count)
    domain_length_value, _ = _scalar_frame_value(data, ("domain_length", "length"), frame_index, frame_count)

    grid_spacing: float | None = None
    domain_length: float | None = None
    scale_source: str | None = None
    n = float(lambda2.shape[0])
    if grid_spacing_value is not None:
        grid_spacing = _finite_float(grid_spacing_value, "grid_spacing")
        if grid_spacing <= 0.0:
            raise ValueError("grid_spacing must be positive")
        scale_source = "grid_spacing"
        if domain_length_value is not None:
            domain_length = _finite_float(domain_length_value, "domain_length")
            if domain_length <= 0.0:
                raise ValueError("domain_length must be positive")
            expected = grid_spacing * n
            if not math.isclose(domain_length, expected, rel_tol=1.0e-12, abs_tol=1.0e-12):
                raise ValueError("grid_spacing_domain_length_mismatch")
        else:
            domain_length = grid_spacing * n
    elif domain_length_value is not None:
        domain_length = _finite_float(domain_length_value, "domain_length")
        if domain_length <= 0.0:
            raise ValueError("domain_length must be positive")
        grid_spacing = domain_length / n
        scale_source = "domain_length"
    else:
        scale_source = "index_units"
        warnings.append("missing_scale_metadata_using_index_units")

    return (
        thickness_diag.FieldBundle(
            lambda2=lambda2,
            g12=g12,
            b_k=b_k,
            pressure_hessian_norm=pressure_hessian_norm,
            beta=float(beta_value),
            beta_source=str(beta_source),
            grid_spacing=grid_spacing,
            domain_length=domain_length,
            scale_source=scale_source,
        ),
        warnings,
    )


def _frame_sources(input_path: Path, max_frames: int | None) -> tuple[list[FrameSource], int]:
    sources: list[FrameSource] = []
    available_frames = 0
    if input_path.is_dir():
        files = sorted(path for path in input_path.iterdir() if path.is_file() and path.suffix.lower() == ".npz")
        if not files:
            raise ValueError(f"no .npz archives found in directory {input_path}")
        for file_path in files:
            data = _load_npz(file_path)
            frame_count = _frame_axis_count(data)
            available_frames += frame_count
            if max_frames is not None and len(sources) >= max_frames:
                continue
            take = frame_count if max_frames is None else min(frame_count, max_frames - len(sources))
            for frame_index in range(take):
                label = f"{file_path.name}#frame{frame_index}"
                sources.append(FrameSource(file_path, label, frame_index, frame_count, data))
        return sources, available_frames

    if not input_path.exists():
        raise FileNotFoundError(f"input path not found: {input_path}")
    if input_path.suffix.lower() != ".npz":
        raise ValueError("input must be a .npz archive or a directory of .npz archives")

    data = _load_npz(input_path)
    frame_count = _frame_axis_count(data)
    available_frames = frame_count
    take = frame_count if max_frames is None else min(frame_count, max_frames)
    for frame_index in range(take):
        label = f"{input_path.name}#frame{frame_index}"
        sources.append(FrameSource(input_path, label, frame_index, frame_count, data))
    return sources, available_frames


def _component_choice(report: dict[str, Any]) -> tuple[int | None, str | None, dict[str, Any] | None]:
    if report.get("status") != "ok":
        return None, None, None

    for key, source in (("min_rho_component", "min_rho_component"), ("min_g12_component", "min_g12_component")):
        component = report.get(key)
        if isinstance(component, dict):
            component_id = component.get("component_id")
            if isinstance(component_id, int) and component_id > 0:
                return int(component_id), source, component

    extremal = report.get("extremal_cells", {})
    if isinstance(extremal, dict):
        min_g12 = extremal.get("min_g12", {})
        if isinstance(min_g12, dict):
            adjacent = min_g12.get("adjacent_component_ids", [])
            if isinstance(adjacent, list):
                for candidate in adjacent:
                    try:
                        component_id = int(candidate)
                    except Exception:
                        continue
                    if component_id > 0:
                        return component_id, "min_g12_adjacent", None

    focus_components = report.get("focus_components", [])
    if isinstance(focus_components, list):
        for component in focus_components:
            if not isinstance(component, dict):
                continue
            component_id = component.get("component_id")
            if isinstance(component_id, int) and component_id > 0:
                return int(component_id), "focus_component_fallback", component

    top_components = report.get("top_components", [])
    if isinstance(top_components, list):
        for component in top_components:
            if not isinstance(component, dict):
                continue
            component_id = component.get("component_id")
            if isinstance(component_id, int) and component_id > 0:
                return int(component_id), "top_component_fallback", component

    return None, None, None


def _component_stats(component: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(component, dict):
        return {}
    return component


def _boundary_stat(component: dict[str, Any], *names: str) -> float | None:
    nested = component.get("boundary_stats")
    if isinstance(nested, dict):
        for name in names:
            value = nested.get(name)
            if value is not None:
                return float(value)
    for name in names:
        value = component.get(name)
        if value is not None:
            return float(value)
    return None


def _gradient_stat(component: dict[str, Any], name: str) -> float | None:
    nested = component.get("gradient_stats")
    if isinstance(nested, dict):
        value = nested.get(name)
        if value is not None:
            return float(value)
    value = component.get(name)
    if value is not None:
        return float(value)
    return None


def _layer_thickness_mean_from_component(
    component_id: int,
    bundle: thickness_diag.FieldBundle,
    lambda2_band: float,
) -> tuple[float | None, list[str]]:
    warnings: list[str] = []
    labels = thickness_diag._label_components(bundle.lambda2 <= bundle.beta)
    grad_x, grad_y, grad_z, grad_mag = thickness_diag._gradient_components(bundle.lambda2, bundle.grid_spacing)
    layer_mask = np.asarray(np.abs(bundle.lambda2) <= float(lambda2_band), dtype=bool)
    summary = thickness_diag._component_summary(
        component_id=component_id,
        labels=labels,
        lambda2=bundle.lambda2,
        grad_mag=grad_mag,
        grad_vec=(grad_x, grad_y, grad_z),
        layer_mask=layer_mask,
        beta=bundle.beta,
        radius=DEFAULT_LAYER_SEARCH_RADIUS_CELLS,
        spacing=bundle.grid_spacing,
    )
    status = str(summary.get("status"))
    thickness_stats = summary.get("thickness_stats")
    if isinstance(thickness_stats, dict):
        physical_mean = thickness_stats.get("transition_thickness_physical_mean")
        if physical_mean is not None:
            return float(physical_mean), warnings
        cells_mean = thickness_stats.get("transition_thickness_cells_mean")
        if cells_mean is not None:
            warnings.append("layer_thickness_mean_fallback_to_cells")
            return float(cells_mean), warnings
    warnings.append(f"layer_thickness_unavailable:{status}")
    return None, warnings


def _frame_report(source: FrameSource, lambda2_band: float, strict: bool) -> dict[str, Any]:
    try:
        bundle, warnings = _optional_frame_bundle(source.data, source.frame_index, source.frame_count)
        component_report = component_diag._build_report(
            source.source_path,
            bundle,
            lambda2_band,
            top_components=8,
            strict=strict,
        )
    except Exception as exc:
        return {
            "frame": source.label,
            "frame_index": source.frame_index,
            "source": str(source.source_path),
            "carrier_id": None,
            "carrier_source": None,
            "boundary_samples": None,
            "cell_count": None,
            "layer_thickness_mean": None,
            "grad_lambda2_mean": None,
            "grad_lambda2_max": None,
            "min_g12": None,
            "rho_min": None,
            "rho_mean": None,
            "warnings": [f"{type(exc).__name__}:{exc}"],
            "status": "missing_required_field",
        }

    row_warnings = list(warnings)
    status = str(component_report.get("status", "missing_required_field"))
    carrier_id, carrier_source, carrier_component = _component_choice(component_report)
    carrier_component = _component_stats(carrier_component)
    true_denominator_kind = _true_denominator_kind(source.data)
    if carrier_id is None:
        row_warnings.append("carrier_component_unavailable")

    boundary_samples = carrier_component.get("boundary_cell_count")
    cell_count = carrier_component.get("cell_count")
    layer_thickness_mean: float | None = None
    if carrier_id is not None and status in {"ok", "no_boundary_cells"}:
        try:
            layer_thickness_mean, extra_warnings = _layer_thickness_mean_from_component(carrier_id, bundle, lambda2_band)
            row_warnings.extend(extra_warnings)
        except Exception as exc:
            row_warnings.append(f"layer_thickness_error:{type(exc).__name__}:{exc}")
            layer_thickness_mean = None

    extremal = component_report.get("extremal_cells", {})
    min_g12 = None
    if isinstance(extremal, dict):
        min_g12_info = extremal.get("min_g12", {})
        if isinstance(min_g12_info, dict) and min_g12_info.get("value") is not None:
            min_g12 = float(min_g12_info["value"])

    rho_min = _boundary_stat(carrier_component, "rho_min")
    rho_mean = _boundary_stat(carrier_component, "rho_mean")
    grad_lambda2_mean = _gradient_stat(carrier_component, "grad_lambda2_mean")
    grad_lambda2_max = _gradient_stat(carrier_component, "grad_lambda2_max")

    if status != "ok":
        row_warnings.append(f"component_status:{status}")

    return {
        "frame": source.label,
        "frame_index": source.frame_index,
        "source": str(source.source_path),
        "carrier_id": None if carrier_id is None else int(carrier_id),
        "carrier_source": carrier_source,
        "true_denominator_kind": true_denominator_kind,
        "boundary_samples": None if boundary_samples is None else int(boundary_samples),
        "cell_count": None if cell_count is None else int(cell_count),
        "layer_thickness_mean": None if layer_thickness_mean is None else float(layer_thickness_mean),
        "grad_lambda2_mean": None if grad_lambda2_mean is None else float(grad_lambda2_mean),
        "grad_lambda2_max": None if grad_lambda2_max is None else float(grad_lambda2_max),
        "min_g12": min_g12,
        "rho_min": rho_min,
        "rho_mean": rho_mean,
        "warnings": sorted(set(row_warnings)),
        "status": status,
    }


def _summarize_rows(rows: list[dict[str, Any]], max_frames: int | None, available_frames: int) -> dict[str, Any]:
    carrier_ids = sorted({row["carrier_id"] for row in rows if row.get("carrier_id") is not None})
    status_counts = Counter(str(row.get("status", "missing_required_field")) for row in rows)
    return {
        "frame_count": len(rows),
        "available_frame_count": available_frames,
        "processed_frame_count": len(rows),
        "truncated": max_frames is not None and len(rows) < available_frames,
        "carrier_id_unique": carrier_ids,
        "carrier_stable": len(carrier_ids) <= 1,
        "status_counts": dict(sorted(status_counts.items())),
    }


def _render_text(payload: dict[str, Any]) -> str:
    lines = [
        f"status: {payload['status']}",
        f"input: {payload['input']}",
        f"frame_count: {payload.get('frame_count')}",
        f"carrier_id_unique: {payload.get('summary', {}).get('carrier_id_unique')}",
    ]
    rows = payload.get("rows", [])
    for row in rows[:5]:
        lines.append(
            f"frame {row['frame']}: carrier_id={row['carrier_id']} "
            f"boundary_samples={row['boundary_samples']} min_g12={row['min_g12']} "
            f"rho_min={row['rho_min']} layer_thickness_mean={row['layer_thickness_mean']}"
        )
    if len(rows) > 5:
        lines.append(f"... {len(rows) - 5} more frames")
    warning_count = len(payload.get("warnings", []))
    if warning_count:
        lines.append(f"warnings: {warning_count}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", type=Path, required=True, help="derived tensor archive or directory of per-frame archives")
    parser.add_argument("--lambda2-band", type=float, default=DEFAULT_LAMBDA2_BAND, help="boundary-layer band for |lambda2|")
    parser.add_argument("--output", type=Path, required=True, help="output JSON path")
    parser.add_argument("--json", action="store_true", help="emit deterministic JSON on stdout")
    parser.add_argument("--strict", action="store_true", help="fail closed when scale metadata is absent or inconsistent")
    parser.add_argument("--max-frames", type=_positive_int, default=None, help="cap the number of frames processed")
    return parser.parse_args()


def _validate_lambda2_band(value: float) -> None:
    if not math.isfinite(value) or value < 0.0:
        raise ValueError("--lambda2-band must be finite and nonnegative")


def main() -> int:
    args = parse_args()
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "input": str(args.input),
        "lambda2_band": float(args.lambda2_band),
        "strict": bool(args.strict),
        "max_frames": None if args.max_frames is None else int(args.max_frames),
        "rows": [],
        "warnings": [],
        "errors": [],
    }

    try:
        _validate_lambda2_band(args.lambda2_band)
        sources, available_frames = _frame_sources(args.input, args.max_frames)
        if not sources:
            raise ValueError("no frames discovered in input")

        rows: list[dict[str, Any]] = []
        for source in sources:
            row = _frame_report(source, float(args.lambda2_band), bool(args.strict))
            rows.append(row)

        payload["rows"] = rows
        payload["frame_count"] = len(rows)
        payload["summary"] = _summarize_rows(rows, args.max_frames, available_frames)
        payload["warnings"] = sorted(
            {
                warning
                for row in rows
                for warning in row.get("warnings", [])
                if warning and isinstance(warning, str)
            }
        )
        payload["errors"] = sorted(
            {
                row["status"]
                for row in rows
                if row.get("status") not in {"ok", "no_boundary_cells"}
            }
        )
        if all(row.get("status") == "ok" for row in rows):
            payload["status"] = "ok" if not payload["warnings"] else "partial"
        elif any(row.get("status") in {"ok", "no_boundary_cells"} for row in rows):
            payload["status"] = "partial"
        else:
            payload["status"] = "missing_required_field"
    except Exception as exc:
        payload["status"] = "missing_required_field"
        payload["errors"] = [f"{type(exc).__name__}:{exc}"]
        payload["rows"] = []
        payload["frame_count"] = 0
        payload["summary"] = {
            "frame_count": 0,
            "available_frame_count": 0,
            "processed_frame_count": 0,
            "truncated": False,
            "carrier_id_unique": [],
            "carrier_stable": True,
            "status_counts": {},
        }

    text = _json_text(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print(_render_text(payload))
    return 0 if payload.get("status") == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
