#!/usr/bin/env python3
"""Standalone Calc 5 boundary-layer thickness diagnostic for NS tensor archives.

The script consumes a derived tensor archive with the arrays

    lambda2, g12, B_k or B_k_max, pressure_hessian_norm, beta

and optional scale metadata in ``grid_spacing`` and/or ``domain_length``.
It labels the sublevel set ``{lambda2 <= beta}``, resolves target component
ids from ``--component-id`` and/or ``--auto-min-g12-adjacent``, and measures
boundary-layer thickness on the layer ``|lambda2| <= lambda2_band``.

The diagnostic is fail-closed. Top-level statuses are:

    missing_required_field, no_boundary_cells, component_not_found,
    no_target_components, no_layer_samples, ok

When available, ``scipy.ndimage.label`` is used for connected-component
labelling; otherwise a deterministic 6-neighbour BFS fallback is used.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_boundary_layer_thickness_diagnostic.py"
CONTRACT = "ns_boundary_layer_thickness_diagnostic"
DEFAULT_LAMBDA2_BAND = 1.0e-3
DEFAULT_MAX_SEARCH_RADIUS_CELLS = 12
BOUNDARY_LAYER_STATUS = "no_boundary_cells"
TARGET_LABEL_STATUS = "component_not_found"
NO_TARGET_STATUS = "no_target_components"
NO_LAYER_STATUS = "no_layer_samples"
OK_STATUS = "ok"

try:  # Optional dependency.
    from scipy.ndimage import distance_transform_edt as scipy_distance_transform_edt
    from scipy.ndimage import label as scipy_label
    from scipy.ndimage import generate_binary_structure as scipy_binary_structure
except Exception:  # pragma: no cover - optional dependency.
    scipy_distance_transform_edt = None
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
    scale_source: str


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
        return {name: np.asarray(data[name]) for name in data.files}


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
    required_keys = ("lambda2", "g12", b_key, "pressure_hessian_norm")
    for key in required_keys:
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
            missing.append("beta")
            beta_value = 0.0
    except Exception as exc:
        missing.append(f"beta:{exc}")
        beta_value = 0.0

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
        return None, [
            "shape_mismatch:"
            + ",".join(str(shape) for shape in (lambda2.shape, g12.shape, b_k.shape, pressure_hessian_norm.shape))
        ]
    if not (
        np.all(np.isfinite(lambda2))
        and np.all(np.isfinite(g12))
        and np.all(np.isfinite(b_k))
        and np.all(np.isfinite(pressure_hessian_norm))
    ):
        return None, ["nonfinite_required_field"]

    try:
        grid_spacing_value, _ = _scalar_metadata(data, "grid_spacing")
        domain_length_value, _ = _scalar_metadata(data, "domain_length", "length")
    except Exception as exc:
        return None, [f"scale_metadata:{exc}"]

    grid_spacing: float | None = None
    domain_length: float | None = None
    scale_source = "index_units"
    n = float(lambda2.shape[0])
    if grid_spacing_value is not None:
        grid_spacing = _finite_float(grid_spacing_value, "grid_spacing")
        if grid_spacing <= 0.0:
            return None, ["grid_spacing_nonpositive"]
        scale_source = "grid_spacing"
        if domain_length_value is not None:
            domain_length = _finite_float(domain_length_value, "domain_length")
            if domain_length <= 0.0:
                return None, ["domain_length_nonpositive"]
            expected = grid_spacing * n
            if not math.isclose(domain_length, expected, rel_tol=1.0e-12, abs_tol=1.0e-12):
                return None, ["grid_spacing_domain_length_mismatch"]
        else:
            domain_length = grid_spacing * n
    elif domain_length_value is not None:
        domain_length = _finite_float(domain_length_value, "domain_length")
        if domain_length <= 0.0:
            return None, ["domain_length_nonpositive"]
        grid_spacing = domain_length / n
        scale_source = "domain_length"
    elif strict:
        return None, ["missing_grid_spacing_or_domain_length"]

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


def _gradient_components(field: np.ndarray, spacing: float | None) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    h = 1.0 if spacing is None else float(spacing)
    edge_order = 2 if min(field.shape) >= 3 else 1
    grad_x, grad_y, grad_z = np.gradient(field, h, h, h, edge_order=edge_order)
    magnitude = np.sqrt(grad_x * grad_x + grad_y * grad_y + grad_z * grad_z)
    return grad_x, grad_y, grad_z, magnitude


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


def _boundary_layer_indices(component_mask: np.ndarray, layer_mask: np.ndarray) -> np.ndarray:
    return np.argwhere(component_mask & layer_mask)


def _component_exists(labels: np.ndarray, component_id: int) -> bool:
    return bool(np.any(labels == component_id))


@lru_cache(maxsize=32)
def _offsets_within_radius(radius: int) -> tuple[tuple[int, int, int, float], ...]:
    offsets: list[tuple[int, int, int, float]] = []
    r = int(radius)
    for dx in range(-r, r + 1):
        for dy in range(-r, r + 1):
            for dz in range(-r, r + 1):
                if dx == 0 and dy == 0 and dz == 0:
                    continue
                dist = math.sqrt(float(dx * dx + dy * dy + dz * dz))
                if dist <= float(r) + 1.0e-12:
                    offsets.append((dx, dy, dz, dist))
    offsets.sort(key=lambda item: (item[3], item[0], item[1], item[2]))
    return tuple(offsets)


def _sample_ray_points(
    start: tuple[int, int, int],
    direction: np.ndarray,
    radius: int,
    shape: tuple[int, int, int],
) -> list[tuple[int, int, int]]:
    if float(np.linalg.norm(direction)) == 0.0:
        return []
    step_count = max(2, int(radius) * 8)
    samples = np.linspace(0.0, float(radius), step_count + 1, dtype=np.float64)
    points: list[tuple[int, int, int]] = []
    previous: tuple[int, int, int] | None = None
    start_vec = np.asarray(start, dtype=np.float64)
    for t in samples[1:]:
        candidate = np.rint(start_vec + t * direction).astype(np.int64)
        idx = (int(candidate[0]), int(candidate[1]), int(candidate[2]))
        if idx == previous:
            continue
        if idx[0] < 0 or idx[1] < 0 or idx[2] < 0:
            break
        if idx[0] >= shape[0] or idx[1] >= shape[1] or idx[2] >= shape[2]:
            break
        points.append(idx)
        previous = idx
    return points


def _local_extremum_index(values: list[float], side: str) -> int | None:
    if len(values) < 3:
        return None
    if side == "positive":
        for index in range(1, len(values) - 1):
            left = values[index - 1]
            center = values[index]
            right = values[index + 1]
            if center >= left and center >= right and (center > left or center > right):
                return index
        return None
    for index in range(1, len(values) - 1):
        left = values[index - 1]
        center = values[index]
        right = values[index + 1]
        if center <= left and center <= right and (center < left or center < right):
            return index
    return None


def _ray_search(
    lambda2: np.ndarray,
    start: tuple[int, int, int],
    grad_vec: np.ndarray,
    side: str,
    beta: float,
    radius: int,
) -> dict[str, Any] | None:
    norm = float(np.linalg.norm(grad_vec))
    if norm <= 0.0:
        return None
    direction = grad_vec / norm
    if side == "negative":
        direction = -direction
    points = _sample_ray_points(start, direction, radius, lambda2.shape)
    if not points:
        return None
    values = [float(lambda2[idx]) for idx in points]
    extremum_index = _local_extremum_index(values, side)
    if extremum_index is not None:
        idx = points[extremum_index]
        return {
            "index": [int(v) for v in idx],
            "distance_cells": float(math.dist(start, idx)),
            "distance_physical": None,
            "method": "ray_local_extremum",
        }
    threshold = beta
    if side == "positive":
        for idx in points:
            if float(lambda2[idx]) > threshold:
                return {
                    "index": [int(v) for v in idx],
                    "distance_cells": float(math.dist(start, idx)),
                    "distance_physical": None,
                    "method": "ray_superlevel",
                }
    else:
        for idx in points:
            if float(lambda2[idx]) < threshold:
                return {
                    "index": [int(v) for v in idx],
                    "distance_cells": float(math.dist(start, idx)),
                    "distance_physical": None,
                    "method": "ray_sublevel",
                }
    return None


def _nearest_side_cell(
    lambda2: np.ndarray,
    start: tuple[int, int, int],
    side: str,
    beta: float,
    radius: int,
    spacing: float | None,
) -> dict[str, Any] | None:
    side_mask = lambda2 > beta if side == "positive" else lambda2 < beta
    side_mask = np.asarray(side_mask, dtype=bool)
    if not np.any(side_mask):
        return None

    if scipy_distance_transform_edt is not None:
        complement = ~side_mask
        distances, indices = scipy_distance_transform_edt(
            complement,
            sampling=1.0 if spacing is None else float(spacing),
            return_indices=True,
        )
        idx = tuple(int(indices[axis][start]) for axis in range(3))
        distance_physical = float(distances[start])
        distance_cells = distance_physical if spacing is None else distance_physical / float(spacing)
        if idx != start and distance_cells <= float(radius) + 1.0e-12:
            return {
                "index": [int(v) for v in idx],
                "distance_cells": float(distance_cells),
                "distance_physical": distance_physical if spacing is not None else None,
                "method": "edt_superlevel",
            }

    best: tuple[float, tuple[int, int, int]] | None = None
    start_vec = np.asarray(start, dtype=np.int64)
    for dx, dy, dz, dist_cells in _offsets_within_radius(int(radius)):
        candidate = start_vec + np.asarray((dx, dy, dz), dtype=np.int64)
        idx = (int(candidate[0]), int(candidate[1]), int(candidate[2]))
        if idx == start:
            continue
        if idx[0] < 0 or idx[1] < 0 or idx[2] < 0:
            continue
        if idx[0] >= lambda2.shape[0] or idx[1] >= lambda2.shape[1] or idx[2] >= lambda2.shape[2]:
            continue
        if not side_mask[idx]:
            continue
        best = (dist_cells, idx)
        break
    if best is None:
        return None
    dist_cells, idx = best
    distance_physical = None if spacing is None else float(dist_cells * float(spacing))
    return {
        "index": [int(v) for v in idx],
        "distance_cells": float(dist_cells),
        "distance_physical": distance_physical,
        "method": "fallback_superlevel",
    }


def _distance_sample(
    lambda2: np.ndarray,
    start: tuple[int, int, int],
    grad_vec: np.ndarray,
    side: str,
    beta: float,
    radius: int,
    spacing: float | None,
) -> dict[str, Any] | None:
    ray = _ray_search(lambda2, start, grad_vec, side, beta, radius)
    if ray is not None:
        if spacing is not None:
            ray["distance_physical"] = float(ray["distance_cells"] * float(spacing))
        return ray
    return _nearest_side_cell(lambda2, start, side, beta, radius, spacing)


def _component_summary(
    component_id: int,
    labels: np.ndarray,
    lambda2: np.ndarray,
    grad_mag: np.ndarray,
    grad_vec: tuple[np.ndarray, np.ndarray, np.ndarray],
    layer_mask: np.ndarray,
    beta: float,
    radius: int,
    spacing: float | None,
) -> dict[str, Any]:
    component_mask = labels == component_id
    component_cells = int(np.count_nonzero(component_mask))
    layer_points = _boundary_layer_indices(component_mask, layer_mask)
    boundary_cell_count = int(layer_points.shape[0])
    summary: dict[str, Any] = {
        "component_id": int(component_id),
        "component_cell_count": component_cells,
        "boundary_cell_count": boundary_cell_count,
        "search_radius_cells": int(radius),
        "status": OK_STATUS,
        "gradient_stats": {
            "grad_lambda2_min": None,
            "grad_lambda2_mean": None,
            "grad_lambda2_max": None,
        },
        "positive_side": {
            "sample_count": 0,
            "distance_cells_min": None,
            "distance_cells_mean": None,
            "distance_cells_max": None,
            "distance_physical_min": None,
            "distance_physical_mean": None,
            "distance_physical_max": None,
            "methods": {},
        },
        "negative_side": {
            "sample_count": 0,
            "distance_cells_min": None,
            "distance_cells_mean": None,
            "distance_cells_max": None,
            "distance_physical_min": None,
            "distance_physical_mean": None,
            "distance_physical_max": None,
            "methods": {},
        },
    }

    if boundary_cell_count == 0:
        summary["status"] = NO_LAYER_STATUS
        return summary

    boundary_grad = grad_mag[component_mask & layer_mask]
    summary["gradient_stats"] = {
        "grad_lambda2_min": float(np.min(boundary_grad)),
        "grad_lambda2_mean": float(np.mean(boundary_grad)),
        "grad_lambda2_max": float(np.max(boundary_grad)),
    }

    pos_distances_cells: list[float] = []
    pos_distances_physical: list[float] = []
    neg_distances_cells: list[float] = []
    neg_distances_physical: list[float] = []
    pos_methods: dict[str, int] = {}
    neg_methods: dict[str, int] = {}
    g_x, g_y, g_z = grad_vec
    for point in layer_points:
        start = (int(point[0]), int(point[1]), int(point[2]))
        vec = np.array([float(g_x[start]), float(g_y[start]), float(g_z[start])], dtype=np.float64)
        positive = _distance_sample(lambda2, start, vec, "positive", beta, radius, spacing)
        negative = _distance_sample(lambda2, start, vec, "negative", beta, radius, spacing)
        if positive is None or negative is None:
            summary["status"] = NO_LAYER_STATUS
            return summary
        pos_distances_cells.append(float(positive["distance_cells"]))
        neg_distances_cells.append(float(negative["distance_cells"]))
        if positive["distance_physical"] is not None:
            pos_distances_physical.append(float(positive["distance_physical"]))
        if negative["distance_physical"] is not None:
            neg_distances_physical.append(float(negative["distance_physical"]))
        pos_methods[str(positive["method"])] = pos_methods.get(str(positive["method"]), 0) + 1
        neg_methods[str(negative["method"])] = neg_methods.get(str(negative["method"]), 0) + 1

    summary["positive_side"] = {
        "sample_count": len(pos_distances_cells),
        "distance_cells_min": float(np.min(pos_distances_cells)),
        "distance_cells_mean": float(np.mean(pos_distances_cells)),
        "distance_cells_max": float(np.max(pos_distances_cells)),
        "distance_physical_min": None if not pos_distances_physical else float(np.min(pos_distances_physical)),
        "distance_physical_mean": None if not pos_distances_physical else float(np.mean(pos_distances_physical)),
        "distance_physical_max": None if not pos_distances_physical else float(np.max(pos_distances_physical)),
        "methods": dict(sorted(pos_methods.items())),
    }
    summary["negative_side"] = {
        "sample_count": len(neg_distances_cells),
        "distance_cells_min": float(np.min(neg_distances_cells)),
        "distance_cells_mean": float(np.mean(neg_distances_cells)),
        "distance_cells_max": float(np.max(neg_distances_cells)),
        "distance_physical_min": None if not neg_distances_physical else float(np.min(neg_distances_physical)),
        "distance_physical_mean": None if not neg_distances_physical else float(np.mean(neg_distances_physical)),
        "distance_physical_max": None if not neg_distances_physical else float(np.max(neg_distances_physical)),
        "methods": dict(sorted(neg_methods.items())),
    }
    pos_min = summary["positive_side"]["distance_cells_min"]
    pos_mean = summary["positive_side"]["distance_cells_mean"]
    pos_max = summary["positive_side"]["distance_cells_max"]
    neg_min = summary["negative_side"]["distance_cells_min"]
    neg_mean = summary["negative_side"]["distance_cells_mean"]
    neg_max = summary["negative_side"]["distance_cells_max"]
    pos_phys_min = summary["positive_side"]["distance_physical_min"]
    pos_phys_mean = summary["positive_side"]["distance_physical_mean"]
    pos_phys_max = summary["positive_side"]["distance_physical_max"]
    neg_phys_min = summary["negative_side"]["distance_physical_min"]
    neg_phys_mean = summary["negative_side"]["distance_physical_mean"]
    neg_phys_max = summary["negative_side"]["distance_physical_max"]
    summary["thickness_stats"] = {
        "sample_count": len(pos_distances_cells),
        "positive_distance_cells_min": pos_min,
        "positive_distance_cells_mean": pos_mean,
        "positive_distance_cells_max": pos_max,
        "negative_distance_cells_min": neg_min,
        "negative_distance_cells_mean": neg_mean,
        "negative_distance_cells_max": neg_max,
        "transition_thickness_cells_min": None if pos_min is None or neg_min is None else float(pos_min + neg_min),
        "transition_thickness_cells_mean": None if pos_mean is None or neg_mean is None else float(pos_mean + neg_mean),
        "transition_thickness_cells_max": None if pos_max is None or neg_max is None else float(pos_max + neg_max),
        "positive_distance_physical_min": pos_phys_min,
        "positive_distance_physical_mean": pos_phys_mean,
        "positive_distance_physical_max": pos_phys_max,
        "negative_distance_physical_min": neg_phys_min,
        "negative_distance_physical_mean": neg_phys_mean,
        "negative_distance_physical_max": neg_phys_max,
        "transition_thickness_physical_min": None if pos_phys_min is None or neg_phys_min is None else float(pos_phys_min + neg_phys_min),
        "transition_thickness_physical_mean": None if pos_phys_mean is None or neg_phys_mean is None else float(pos_phys_mean + neg_phys_mean),
        "transition_thickness_physical_max": None if pos_phys_max is None or neg_phys_max is None else float(pos_phys_max + neg_phys_max),
    }
    return summary


def _normalize_component_ids(values: list[int]) -> list[int]:
    ordered: list[int] = []
    seen: set[int] = set()
    for value in values:
        if value in seen:
            continue
        ordered.append(int(value))
        seen.add(int(value))
    return ordered


def _resolve_target_component_ids(
    args: argparse.Namespace,
    labels: np.ndarray,
    boundary_mask: np.ndarray,
    g12: np.ndarray,
) -> tuple[list[int], dict[str, Any] | None, list[int], list[str] | None]:
    component_count = int(labels.max())
    explicit = _normalize_component_ids([int(value) for value in args.component_id])
    auto_info: dict[str, Any] | None = None
    missing: list[int] = []

    if args.auto_min_g12_adjacent:
        if not np.any(boundary_mask):
            return [], None, [], [BOUNDARY_LAYER_STATUS]
        boundary_indices = np.argwhere(boundary_mask)
        boundary_g12 = g12[boundary_mask]
        min_value = float(np.min(boundary_g12))
        winners = boundary_indices[boundary_g12 == min_value]
        winner = winners[np.lexsort((winners[:, 2], winners[:, 1], winners[:, 0]))][0]
        adjacent = _adjacent_component_ids(labels, winner)
        auto_info = {
            "index": [int(v) for v in winner.tolist()],
            "value": min_value,
            "component_id": int(labels[tuple(int(v) for v in winner.tolist())]),
            "adjacent_component_ids": adjacent,
            "in_component_set": int(labels[tuple(int(v) for v in winner.tolist())]) > 0,
        }
        for component_id in adjacent:
            if component_id <= 0:
                continue
            explicit.append(int(component_id))

    resolved = _normalize_component_ids(explicit)
    if not resolved:
        return [], auto_info, [], None

    for component_id in resolved:
        if component_id <= 0 or component_id > component_count or not _component_exists(labels, component_id):
            missing.append(int(component_id))
    if missing:
        return resolved, auto_info, missing, None
    return resolved, auto_info, [], None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--lambda2-band", type=float, default=DEFAULT_LAMBDA2_BAND, help="boundary-layer band for |lambda2|")
    parser.add_argument("--beta", type=float, default=None, help="override beta threshold from the archive")
    parser.add_argument(
        "--component-id",
        action="append",
        type=_positive_int,
        default=[],
        help="target component id; repeatable",
    )
    parser.add_argument(
        "--auto-min-g12-adjacent",
        action="store_true",
        help="also include component ids adjacent to the min-g12 boundary cell",
    )
    parser.add_argument(
        "--max-search-radius-cells",
        type=_positive_int,
        default=DEFAULT_MAX_SEARCH_RADIUS_CELLS,
        help="maximum ray / fallback search radius measured in grid cells",
    )
    parser.add_argument("--strict", action="store_true", help="require scale metadata and fail closed on its absence")
    parser.add_argument("--json", action="store_true", help="emit deterministic JSON on stdout")
    parser.add_argument("--output", type=Path, default=None, help="optional path to write the JSON payload")
    return parser.parse_args()


def _render_text(payload: dict[str, Any]) -> str:
    lines = [
        f"status: {payload['status']}",
        f"input: {payload['input']}",
        f"beta: {payload['beta']} ({payload['beta_source']})",
        f"lambda2_band: {payload['lambda2_band']}",
        f"global_boundary_cell_count: {payload.get('global_boundary_cell_count')}",
        f"target_component_ids: {payload.get('target_component_ids')}",
    ]
    auto = payload.get("auto_min_g12_boundary_cell")
    if auto is not None:
        lines.append(
            "auto_min_g12_boundary_cell: "
            + str(auto.get("index"))
            + " value="
            + str(auto.get("value"))
            + " adjacent="
            + str(auto.get("adjacent_component_ids"))
        )
    for component in payload.get("components", []):
        lines.append(
            f"component {component['component_id']}: "
            f"boundary_cell_count={component['boundary_cell_count']} "
            f"positive_min={component['positive_side']['distance_cells_min']} "
            f"negative_min={component['negative_side']['distance_cells_min']}"
        )
    return "\n".join(lines)


def _json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _build_payload(args: argparse.Namespace, bundle: FieldBundle) -> dict[str, Any]:
    lambda2 = bundle.lambda2
    g12 = bundle.g12
    labels = _label_components(lambda2 <= bundle.beta)
    boundary_mask = np.abs(lambda2) <= float(args.lambda2_band)
    boundary_mask_source = "absolute_lambda2_band"
    if not np.any(boundary_mask):
        boundary_mask = np.asarray(lambda2 <= bundle.beta, dtype=bool)
        boundary_mask_source = "beta_sublevel_fallback"
    global_boundary_cell_count = int(np.count_nonzero(boundary_mask))

    base: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "input": str(args.input),
        "status": OK_STATUS,
        "strict": bool(args.strict),
        "beta": float(bundle.beta),
        "beta_source": bundle.beta_source,
        "lambda2_band": float(args.lambda2_band),
        "max_search_radius_cells": int(args.max_search_radius_cells),
        "shape": [int(v) for v in lambda2.shape],
        "grid_spacing": None if bundle.grid_spacing is None else float(bundle.grid_spacing),
        "domain_length": None if bundle.domain_length is None else float(bundle.domain_length),
        "scale_source": bundle.scale_source,
        "global_boundary_cell_count": global_boundary_cell_count,
        "boundary_mask_source": boundary_mask_source,
        "target_component_ids_requested": _normalize_component_ids([int(v) for v in args.component_id]),
        "target_component_ids": [],
        "target_components": [],
        "auto_min_g12_boundary_cell": None,
        "components": [],
        "diagnostic_metadata": {
            "diagnostic": False,
            "promoted": False,
            "theorem_promotion": False,
            "candidate_only": True,
        },
    }

    if global_boundary_cell_count == 0:
        base["status"] = BOUNDARY_LAYER_STATUS
        return base

    target_ids, auto_info, missing, _ = _resolve_target_component_ids(args, labels, boundary_mask, g12)
    base["auto_min_g12_boundary_cell"] = auto_info
    if missing:
        base["status"] = TARGET_LABEL_STATUS
        base["target_component_ids"] = target_ids
        base["missing_component_ids"] = missing
        return base
    if not target_ids:
        if args.auto_min_g12_adjacent:
            base["status"] = NO_TARGET_STATUS
            base["errors"] = ["no_target_components_from_auto_min_g12_adjacent"]
            base["auto_min_g12_boundary_cell"] = auto_info
        else:
            base["status"] = NO_TARGET_STATUS
        return base

    grad_x, grad_y, grad_z, grad_mag = _gradient_components(lambda2, bundle.grid_spacing)
    components: list[dict[str, Any]] = []
    component_warnings: list[dict[str, Any]] = []
    for component_id in target_ids:
        component = _component_summary(
            component_id=component_id,
            labels=labels,
            lambda2=lambda2,
            grad_mag=grad_mag,
            grad_vec=(grad_x, grad_y, grad_z),
            layer_mask=boundary_mask,
            beta=bundle.beta,
            radius=int(args.max_search_radius_cells),
            spacing=bundle.grid_spacing,
        )
        components.append(component)
        if component["status"] != OK_STATUS:
            component_warnings.append(
                {
                    "component_id": int(component_id),
                    "status": str(component["status"]),
                }
            )

    base["target_component_ids"] = target_ids
    base["components"] = components
    base["target_components"] = components
    base["component_warnings"] = component_warnings
    base["component_warning_count"] = len(component_warnings)
    if components and all(component["status"] != OK_STATUS for component in components):
        base["status"] = NO_LAYER_STATUS
    return base


def main() -> int:
    args = parse_args()
    payload = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "input": str(args.input),
        "lambda2_band": float(args.lambda2_band),
        "beta": None if args.beta is None else float(args.beta),
        "strict": bool(args.strict),
        "max_search_radius_cells": int(args.max_search_radius_cells),
    }

    if not math.isfinite(args.lambda2_band) or args.lambda2_band < 0.0:
        payload.update({"status": "missing_required_field", "errors": ["invalid_lambda2_band"]})
    else:
        bundle, missing = _load_fields(args.input, args.beta, args.strict)
        if bundle is None:
            payload.update({"status": "missing_required_field", "errors": sorted(set(missing))})
        else:
            payload.update(_build_payload(args, bundle))

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
