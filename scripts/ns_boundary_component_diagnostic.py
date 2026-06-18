#!/usr/bin/env python3
"""Standalone componentwise NS boundary diagnostic.

The script consumes a derived archive produced by
``scripts/ns_boundary_derived_tensor_archive.py`` and reports connected
components of ``{lambda2 <= beta}`` together with boundary-layer statistics on
``|lambda2| <= lambda2_band``.

It is fail-closed: the top-level status is one of
``missing_required_field``, ``no_boundary_cells``, or ``ok``.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_boundary_component_diagnostic.py"
PRODUCER_NAME = "scripts/ns_boundary_derived_tensor_archive.py"
DEFAULT_LAMBDA2_BAND = 1.0e-6
DEFAULT_TOP_COMPONENTS = 10

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
    b_k: np.ndarray
    pressure_hessian_norm: np.ndarray
    beta: float
    beta_source: str
    grid_spacing: float | None
    domain_length: float | None
    scale_source: str | None


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
            for key in ("domain_length", "grid_spacing", "N", "axis_order"):
                if key in meta and key not in payload:
                    payload[key] = np.asarray(meta[key])
    return payload


def _squeeze_single_snapshot(field: np.ndarray) -> np.ndarray:
    if field.ndim == 4 and field.shape[0] == 1:
        return np.asarray(field[0])
    return np.asarray(field)


def _load_fields(path: Path, beta_override: float | None, strict: bool) -> tuple[FieldBundle | None, list[str]]:
    missing: list[str] = []
    try:
        data = _load_npz(path)
    except FileNotFoundError:
        return None, ["input_archive"]
    except Exception as exc:
        return None, [f"input_archive:{exc}"]

    b_key = "B_k" if "B_k" in data else "B_k_max" if "B_k_max" in data else "B_k"
    required_keys = ["lambda2", "g12", b_key, "pressure_hessian_norm"]
    for key in required_keys:
        if key not in data:
            missing.append(key)
    beta_source = "cli"
    beta_value: float | None = None
    try:
        if beta_override is not None:
            beta_value = _finite_float(beta_override, "--beta")
        elif "beta" in data:
            beta_source = "archive"
            beta_value = _finite_float(np.asarray(data["beta"]).item(), "beta")
        else:
            missing.append("beta")
    except Exception as exc:
        missing.append(f"beta:{exc}")

    if missing:
        return None, missing

    try:
        lambda2 = _squeeze_single_snapshot(np.asarray(data["lambda2"], dtype=np.float64))
        g12 = _squeeze_single_snapshot(np.asarray(data["g12"], dtype=np.float64))
        b_k = _squeeze_single_snapshot(np.asarray(data[b_key], dtype=np.float64))
        pressure_hessian_norm = _squeeze_single_snapshot(np.asarray(data["pressure_hessian_norm"], dtype=np.float64))
    except Exception as exc:
        return None, [f"field_cast:{exc}"]

    if lambda2.ndim != 3:
        return None, [f"unsupported_field_rank:{lambda2.shape!r}"]
    if not (lambda2.shape == g12.shape == b_k.shape == pressure_hessian_norm.shape):
        return None, [f"shape_mismatch:{lambda2.shape!r},{g12.shape!r},{b_k.shape!r},{pressure_hessian_norm.shape!r}"]
    if not (np.all(np.isfinite(lambda2)) and np.all(np.isfinite(g12)) and np.all(np.isfinite(b_k)) and np.all(np.isfinite(pressure_hessian_norm))):
        return None, ["nonfinite_required_field"]

    try:
        grid_spacing_value, _ = _scalar_metadata(data, "grid_spacing")
        domain_length_value, _ = _scalar_metadata(data, "domain_length", "length")
    except Exception as exc:
        return None, [f"scale_metadata:{exc}"]
    grid_spacing = None
    domain_length = None
    scale_source = None
    if grid_spacing_value is not None:
        grid_spacing = _finite_float(grid_spacing_value, "grid_spacing")
        if grid_spacing <= 0.0:
            return None, ["grid_spacing_nonpositive"]
        scale_source = "grid_spacing"
        if domain_length_value is not None:
            domain_length = _finite_float(domain_length_value, "domain_length")
            if domain_length <= 0.0:
                return None, ["domain_length_nonpositive"]
            expected = grid_spacing * float(lambda2.shape[0])
            if not math.isclose(domain_length, expected, rel_tol=1.0e-12, abs_tol=1.0e-12):
                return None, ["grid_spacing_domain_length_mismatch"]
        else:
            domain_length = grid_spacing * float(lambda2.shape[0])
    elif domain_length_value is not None:
        domain_length = _finite_float(domain_length_value, "domain_length")
        if domain_length <= 0.0:
            return None, ["domain_length_nonpositive"]
        grid_spacing = domain_length / float(lambda2.shape[0])
        scale_source = "domain_length"
    elif strict:
        return None, ["missing_grid_spacing_or_domain_length"]
    else:
        scale_source = "index_units"

    return (
        FieldBundle(
            lambda2=lambda2,
            g12=g12,
            b_k=b_k,
            pressure_hessian_norm=pressure_hessian_norm,
            beta=float(beta_value),
            beta_source=beta_source,
            grid_spacing=grid_spacing,
            domain_length=domain_length,
            scale_source=scale_source,
        ),
        [],
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


def _gradient_magnitude(field: np.ndarray, spacing: float | None) -> np.ndarray:
    h = 1.0 if spacing is None else float(spacing)
    dx = (np.roll(field, -1, axis=0) - np.roll(field, 1, axis=0)) / (2.0 * h)
    dy = (np.roll(field, -1, axis=1) - np.roll(field, 1, axis=1)) / (2.0 * h)
    dz = (np.roll(field, -1, axis=2) - np.roll(field, 1, axis=2)) / (2.0 * h)
    return np.sqrt(dx * dx + dy * dy + dz * dz)


def _adjacent_component_ids(labels: np.ndarray, index: np.ndarray) -> list[int]:
    x, y, z = (int(index[0]), int(index[1]), int(index[2]))
    shape = labels.shape
    ids: set[int] = set()
    center = int(labels[x, y, z])
    if center > 0:
        ids.add(center)
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
        component_id = int(labels[nx, ny, nz])
        if component_id > 0:
            ids.add(component_id)
    return sorted(ids)


def _physical_value(value: float | None) -> float | None:
    return None if value is None else float(value)


def _summarize_component(
    component_id: int,
    cell_count: int,
    boundary_count: int,
    bbox_min: np.ndarray,
    bbox_max: np.ndarray,
    g12_min: float,
    g12_sum: float,
    g12_max: float,
    rho_min: float,
    rho_sum: float,
    rho_max: float,
    grad_min: float,
    grad_sum: float,
    grad_max: float,
    spacing: float | None,
) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "component_id": int(component_id),
        "cell_count": int(cell_count),
        "volume_cells": int(cell_count),
        "volume_physical": _physical_value(cell_count * (spacing**3) if spacing is not None else None),
        "bbox_index_min": [int(v) for v in bbox_min.tolist()],
        "bbox_index_max": [int(v) for v in bbox_max.tolist()],
        "bbox_diameter_cells": float(np.max(bbox_max - bbox_min + 1)),
        "bbox_diameter_physical": _physical_value(float(np.max(bbox_max - bbox_min + 1)) * spacing if spacing is not None else None),
        "boundary_cell_count": int(boundary_count),
        "boundary_g12_min": None,
        "boundary_g12_mean": None,
        "boundary_g12_max": None,
        "boundary_rho_min": None,
        "boundary_rho_mean": None,
        "boundary_rho_max": None,
        "boundary_grad_lambda2_min": None,
        "boundary_grad_lambda2_mean": None,
        "boundary_grad_lambda2_max": None,
    }
    summary["volume_stats"] = {
        "cell_count": summary["cell_count"],
        "volume_cells": summary["volume_cells"],
        "volume_physical": summary["volume_physical"],
        "bbox_index_min": summary["bbox_index_min"],
        "bbox_index_max": summary["bbox_index_max"],
        "bbox_diameter_cells": summary["bbox_diameter_cells"],
        "bbox_diameter_physical": summary["bbox_diameter_physical"],
    }
    summary["boundary_stats"] = {
        "boundary_cell_count": summary["boundary_cell_count"],
        "g12_min": None,
        "g12_mean": None,
        "g12_max": None,
        "rho_min": None,
        "rho_mean": None,
        "rho_max": None,
    }
    summary["gradient_stats"] = {
        "grad_lambda2_min": None,
        "grad_lambda2_mean": None,
        "grad_lambda2_max": None,
    }
    if boundary_count > 0:
        summary.update(
            {
                "boundary_g12_min": float(g12_min),
                "boundary_g12_mean": float(g12_sum / boundary_count),
                "boundary_g12_max": float(g12_max),
                "boundary_rho_min": float(rho_min),
                "boundary_rho_mean": float(rho_sum / boundary_count),
                "boundary_rho_max": float(rho_max),
                "boundary_grad_lambda2_min": float(grad_min),
                "boundary_grad_lambda2_mean": float(grad_sum / boundary_count),
                "boundary_grad_lambda2_max": float(grad_max),
            }
        )
        summary["boundary_stats"].update(
            {
                "g12_min": float(g12_min),
                "g12_mean": float(g12_sum / boundary_count),
                "g12_max": float(g12_max),
                "rho_min": float(rho_min),
                "rho_mean": float(rho_sum / boundary_count),
                "rho_max": float(rho_max),
            }
        )
        summary["gradient_stats"].update(
            {
                "grad_lambda2_min": float(grad_min),
                "grad_lambda2_mean": float(grad_sum / boundary_count),
                "grad_lambda2_max": float(grad_max),
            }
        )
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="derived tensor archive produced by the boundary tensor script")
    parser.add_argument("--lambda2-band", type=float, default=DEFAULT_LAMBDA2_BAND, help="boundary-layer band for |lambda2|")
    parser.add_argument("--beta", type=float, default=None, help="override beta threshold")
    parser.add_argument("--strict", action="store_true", help="fail on missing physical scale metadata")
    parser.add_argument("--json", action="store_true", help="emit JSON on stdout")
    parser.add_argument("--top-components", type=_positive_int, default=DEFAULT_TOP_COMPONENTS, help="number of largest components to include")
    parser.add_argument("--output", type=Path, default=None, help="optional JSON output path")
    return parser.parse_args()


def _render_text(payload: dict[str, Any]) -> str:
    lines = [
        f"status: {payload['status']}",
        f"input: {payload['input']}",
        f"lambda2_band: {payload['lambda2_band']}",
        f"beta: {payload['beta']} ({payload['beta_source']})",
        f"component_count: {payload.get('component_count')}",
        f"boundary_cell_count: {payload.get('boundary_cell_count')}",
    ]
    extremal = payload.get("extremal_cells", {})
    if "min_g12" in extremal:
        lines.append(
            "min_g12_component: "
            + str(extremal["min_g12"].get("component_id"))
            + " cell="
            + str(extremal["min_g12"].get("index"))
            + " value="
            + str(extremal["min_g12"].get("value"))
        )
    if "min_rho" in extremal:
        lines.append(
            "min_rho_component: "
            + str(extremal["min_rho"].get("component_id"))
            + " cell="
            + str(extremal["min_rho"].get("index"))
            + " value="
            + str(extremal["min_rho"].get("value"))
        )
    lines.append(f"same_component: {extremal.get('same_component')}")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    payload = {
        "script": SCRIPT_NAME,
        "producer": PRODUCER_NAME,
        "input": str(args.input),
        "lambda2_band": float(args.lambda2_band),
        "strict": bool(args.strict),
        "top_components": int(args.top_components),
    }

    if not math.isfinite(args.lambda2_band) or args.lambda2_band < 0.0:
        payload.update({"status": "missing_required_field", "errors": ["invalid_lambda2_band"]})
    else:
        bundle, missing = _load_fields(args.input, args.beta, args.strict)
        if bundle is None:
            payload.update({"status": "missing_required_field", "errors": sorted(set(missing))})
        else:
            report = _build_report(args.input, bundle, args.lambda2_band, args.top_components, args.strict)
            payload.update(report)

    text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print(_render_text(payload))
    return 0 if payload.get("status") == "ok" else 1


def _build_report(input_path: Path, bundle: FieldBundle, lambda2_band: float, top_components: int, strict: bool) -> dict[str, Any]:
    lambda2 = bundle.lambda2
    g12 = bundle.g12
    b_k = bundle.b_k
    pressure_hessian_norm = bundle.pressure_hessian_norm
    rho = b_k / (1.0 + pressure_hessian_norm)

    if np.any(~np.isfinite(rho)) or np.any((1.0 + pressure_hessian_norm) <= 0.0):
        return {"status": "missing_required_field", "errors": ["invalid_rho_field"]}

    threshold_mask = np.asarray(lambda2 <= bundle.beta, dtype=bool)
    labels = _label_components(threshold_mask)
    component_count = int(labels.max())
    boundary_mask = np.asarray(np.abs(lambda2) <= lambda2_band, dtype=bool)
    boundary_cell_count = int(np.count_nonzero(boundary_mask))

    cell_counts = np.bincount(labels.ravel(), minlength=component_count + 1)[1:]
    labels_flat = labels.ravel()

    # Component bounding boxes.
    bbox_min = np.full((component_count + 1, 3), np.iinfo(np.int32).max, dtype=np.int32)
    bbox_max = np.full((component_count + 1, 3), np.iinfo(np.int32).min, dtype=np.int32)
    active_flat = labels_flat > 0
    active_ids = labels_flat[active_flat]
    active_coords = np.nonzero(active_flat)[0]
    if active_ids.size:
        coords = np.unravel_index(active_coords, labels.shape)
        for axis in range(3):
            axis_coords = np.asarray(coords[axis], dtype=np.int32)
            np.minimum.at(bbox_min[:, axis], active_ids, axis_coords)
            np.maximum.at(bbox_max[:, axis], active_ids, axis_coords)

    # Boundary component statistics.
    boundary_flat = boundary_mask.ravel()
    boundary_ids = labels_flat[boundary_flat]
    boundary_g12 = g12.ravel()[boundary_flat]
    boundary_rho = rho.ravel()[boundary_flat]
    boundary_grad = _gradient_magnitude(lambda2, bundle.grid_spacing).ravel()[boundary_flat]

    bcount = np.bincount(boundary_ids, minlength=component_count + 1)
    g12_sum = np.bincount(boundary_ids, weights=boundary_g12, minlength=component_count + 1)
    rho_sum = np.bincount(boundary_ids, weights=boundary_rho, minlength=component_count + 1)
    grad_sum = np.bincount(boundary_ids, weights=boundary_grad, minlength=component_count + 1)

    g12_min = np.full(component_count + 1, np.inf, dtype=np.float64)
    g12_max = np.full(component_count + 1, -np.inf, dtype=np.float64)
    rho_min = np.full(component_count + 1, np.inf, dtype=np.float64)
    rho_max = np.full(component_count + 1, -np.inf, dtype=np.float64)
    grad_min = np.full(component_count + 1, np.inf, dtype=np.float64)
    grad_max = np.full(component_count + 1, -np.inf, dtype=np.float64)
    if boundary_ids.size:
        np.minimum.at(g12_min, boundary_ids, boundary_g12)
        np.maximum.at(g12_max, boundary_ids, boundary_g12)
        np.minimum.at(rho_min, boundary_ids, boundary_rho)
        np.maximum.at(rho_max, boundary_ids, boundary_rho)
        np.minimum.at(grad_min, boundary_ids, boundary_grad)
        np.maximum.at(grad_max, boundary_ids, boundary_grad)

    if boundary_cell_count == 0:
        status = "no_boundary_cells"
        extremal: dict[str, Any] = {"same_component": None}
    else:
        boundary_indices = np.argwhere(boundary_mask)
        boundary_g12_min_value = float(np.min(boundary_g12))
        boundary_rho_min_value = float(np.min(boundary_rho))

        g12_winners = boundary_indices[boundary_g12 == boundary_g12_min_value]
        rho_winners = boundary_indices[boundary_rho == boundary_rho_min_value]
        g12_winner = g12_winners[np.lexsort((g12_winners[:, 2], g12_winners[:, 1], g12_winners[:, 0]))][0]
        rho_winner = rho_winners[np.lexsort((rho_winners[:, 2], rho_winners[:, 1], rho_winners[:, 0]))][0]
        g12_label = int(labels[tuple(int(v) for v in g12_winner)])
        rho_label = int(labels[tuple(int(v) for v in rho_winner)])
        g12_component = None if g12_label == 0 else g12_label
        rho_component = None if rho_label == 0 else rho_label
        extremal = {
            "min_g12": {
                "index": [int(v) for v in g12_winner.tolist()],
                "value": boundary_g12_min_value,
                "component_id": g12_component,
                "adjacent_component_ids": _adjacent_component_ids(labels, g12_winner),
                "in_component_set": g12_component is not None,
            },
            "min_rho": {
                "index": [int(v) for v in rho_winner.tolist()],
                "value": boundary_rho_min_value,
                "component_id": rho_component,
                "adjacent_component_ids": _adjacent_component_ids(labels, rho_winner),
                "in_component_set": rho_component is not None,
            },
            "same_component": None if g12_component is None or rho_component is None else g12_component == rho_component,
        }
        status = "ok"

    ids = np.arange(1, component_count + 1, dtype=np.int32)
    if component_count:
        order = np.lexsort((ids, -cell_counts))
        top_ids = ids[order[: min(top_components, component_count)]]
    else:
        top_ids = np.asarray([], dtype=np.int32)

    component_summaries = [
        _summarize_component(
            int(component_id),
            int(cell_counts[component_id - 1]),
            int(bcount[component_id]),
            bbox_min[component_id],
            bbox_max[component_id],
            float(g12_min[component_id]),
            float(g12_sum[component_id]),
            float(g12_max[component_id]),
            float(rho_min[component_id]),
            float(rho_sum[component_id]),
            float(rho_max[component_id]),
            float(grad_min[component_id]),
            float(grad_sum[component_id]),
            float(grad_max[component_id]),
            bundle.grid_spacing,
        )
        for component_id in top_ids.tolist()
    ]

    focus_ids = []
    if boundary_cell_count:
        for component_id in (extremal["min_g12"]["component_id"], extremal["min_rho"]["component_id"]):
            if isinstance(component_id, int):
                focus_ids.append(component_id)
        focus_ids = sorted(set(focus_ids))
    focus_components = []
    for component_id in focus_ids:
        if component_id <= 0:
            continue
        focus_components.append(
            _summarize_component(
                int(component_id),
                int(cell_counts[component_id - 1]),
                int(bcount[component_id]),
                bbox_min[component_id],
                bbox_max[component_id],
                float(g12_min[component_id]),
                float(g12_sum[component_id]),
                float(g12_max[component_id]),
                float(rho_min[component_id]),
                float(rho_sum[component_id]),
                float(rho_max[component_id]),
                float(grad_min[component_id]),
                float(grad_sum[component_id]),
                float(grad_max[component_id]),
                bundle.grid_spacing,
            )
        )

    payload: dict[str, Any] = {
        "status": status,
        "input": str(input_path),
        "beta": float(bundle.beta),
        "beta_source": bundle.beta_source,
        "lambda2_band": float(lambda2_band),
        "strict": bool(strict),
        "shape": [int(v) for v in lambda2.shape],
        "grid_spacing": _physical_value(bundle.grid_spacing),
        "domain_length": _physical_value(bundle.domain_length),
        "scale_source": bundle.scale_source,
        "component_count": component_count,
        "boundary_cell_count": boundary_cell_count,
        "boundary_component_count": int(np.count_nonzero(bcount[1:])),
        "extremal_cells": extremal,
        "top_components": component_summaries,
        "focus_components": focus_components,
        "same_component": extremal.get("same_component"),
        "min_g12_component": focus_components[0] if focus_components else None,
        "min_rho_component": None,
        "producer": PRODUCER_NAME,
        "script": SCRIPT_NAME,
    }
    if boundary_cell_count:
        min_g12_id = extremal["min_g12"]["component_id"]
        min_rho_id = extremal["min_rho"]["component_id"]
        by_id = {component["component_id"]: component for component in focus_components}
        payload["min_g12_component"] = by_id.get(min_g12_id)
        payload["min_rho_component"] = by_id.get(min_rho_id)
    if bundle.scale_source == "index_units":
        payload["notes"] = [
            "grid_spacing/domain_length metadata absent; physical volumes and diameters are omitted",
        ]
    return payload


if __name__ == "__main__":
    raise SystemExit(main())
