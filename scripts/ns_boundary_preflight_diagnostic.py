#!/usr/bin/env python3
"""Fail-closed boundary diagnostics for raw NS tensor data.

This script inspects one or more raw DNS artifacts in ``.npz`` or flat ``.csv``
form and reports three boundary diagnostics:

1. ``min g12`` on the ``|lambda2| <= band`` boundary layer.
2. ``rho = B_k / (1 + pressure_hessian_norm)`` on that same boundary layer.
3. Betti-0 connected-component counts of ``{lambda2 <= beta(t)}``.

Fail-closed archive contract:

- ``lambda2`` is required for the boundary mask and the Betti-0 threshold set.
- ``g12`` is required for ``min g12`` on the boundary layer.
- ``B_k`` and ``pressure_hessian_norm`` are required for ``rho`` on the boundary layer.
- Betti-0 requires ``beta(t)`` data or ``--beta-value``; missing both is fatal.

It is diagnostic only.  In strict mode, missing files, missing columns/keys,
shape mismatches, empty required layers, unsupported layouts, or a missing
Betti-0 threshold source are fatal.  No numeric results are fabricated when
the required data are absent.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import numpy as np


DEFAULT_LAMBDA2_BAND = 1.0e-6
DEFAULT_TIME_COL = "time"
DEFAULT_INDEX_COLS = ("i", "j", "k")
DEFAULT_LAMBDA2_KEY = "lambda2"
DEFAULT_G12_KEY = "g12"
DEFAULT_B_KEY = "B_k"
DEFAULT_PRESSURE_HESSIAN_KEY = "pressure_hessian_norm"
DEFAULT_BETA_KEY = "beta"


def _input_contract_lines(args: argparse.Namespace | None = None) -> list[str]:
    lambda2_name = DEFAULT_LAMBDA2_KEY if args is None else args.lambda2_key
    g12_name = DEFAULT_G12_KEY if args is None else args.g12_key
    b_name = DEFAULT_B_KEY if args is None else args.b_key
    pressure_name = DEFAULT_PRESSURE_HESSIAN_KEY if args is None else args.pressure_hessian_key
    beta_name = DEFAULT_BETA_KEY if args is None else args.beta_key
    return [
        "input contract:",
        f"  min_g12: requires {lambda2_name} and {g12_name} as .npz keys or .csv columns.",
        f"  rho: requires {lambda2_name}, {b_name}, and {pressure_name} as .npz keys or .csv columns.",
        f"  Betti-0: requires {lambda2_name} plus {beta_name} data or --beta-value.",
        "  layout: .npz must provide matching tensor shapes; .csv must provide a full 3D grid per slice.",
    ]


def _contract_summary(args: argparse.Namespace | None = None) -> dict[str, Any]:
    lambda2_name = DEFAULT_LAMBDA2_KEY if args is None else args.lambda2_key
    g12_name = DEFAULT_G12_KEY if args is None else args.g12_key
    b_name = DEFAULT_B_KEY if args is None else args.b_key
    pressure_name = DEFAULT_PRESSURE_HESSIAN_KEY if args is None else args.pressure_hessian_key
    beta_name = DEFAULT_BETA_KEY if args is None else args.beta_key
    return {
        "min_g12": {
            "required": [lambda2_name, g12_name],
            "meaning": f"boundary min({g12_name}) on |{lambda2_name}| <= band",
        },
        "rho": {
            "required": [lambda2_name, b_name, pressure_name],
            "meaning": f"rho = {b_name} / (1 + {pressure_name}) on the same boundary layer",
        },
        "betti0": {
            "required": [lambda2_name, f"{beta_name} or --beta-value"],
            "meaning": f"Betti-0 connected-component count of {{{lambda2_name} <= beta(t)}}",
        },
    }


@dataclass(frozen=True)
class SliceDiagnostics:
    slice_index: int
    time_label: str
    time_value: float | None
    boundary_cells: int
    min_g12_boundary: float | None
    rho_min_boundary: float | None
    rho_mean_boundary: float | None
    rho_max_boundary: float | None
    betti0: int | None
    beta_value: float | None


@dataclass(frozen=True)
class FileDiagnostics:
    path: str
    format: str
    status: str
    boundary_band: float
    beta_source: str
    slices: list[SliceDiagnostics]
    missing_files: list[str]
    missing_columns: list[str]
    errors: list[str]


def _is_supported_file(path: Path) -> bool:
    return path.suffix.lower() in {".npz", ".csv"}


def _as_float(value: Any) -> float:
    if isinstance(value, np.generic):
        return float(value.item())
    return float(value)


def _parse_index(value: str, label: str) -> int:
    try:
        parsed = float(value)
    except ValueError as exc:
        raise ValueError(f"{label} must be an integer-like value, got {value!r}") from exc
    if not math.isfinite(parsed) or not parsed.is_integer():
        raise ValueError(f"{label} must be an integer-like value, got {value!r}")
    return int(parsed)


def _sorted_unique(values: list[int]) -> list[int]:
    return sorted(set(values))


def _load_npz_bundle(path: Path, args: argparse.Namespace) -> tuple[dict[str, np.ndarray], str, list[str]]:
    with np.load(path, allow_pickle=False) as data:
        keys = set(data.files)
        required = {
            args.lambda2_key,
            args.g12_key,
            args.b_key,
            args.pressure_hessian_key,
        }
        if args.beta_value is None:
            required.add(args.beta_key)
        missing = sorted(key for key in required if key not in keys)
        if missing:
            return {}, "npz", missing

        bundle = {
            args.lambda2_key: np.asarray(data[args.lambda2_key]),
            args.g12_key: np.asarray(data[args.g12_key]),
            args.b_key: np.asarray(data[args.b_key]),
            args.pressure_hessian_key: np.asarray(data[args.pressure_hessian_key]),
        }
        if args.beta_key in keys:
            bundle[args.beta_key] = np.asarray(data[args.beta_key])
        if args.time_key in keys:
            bundle[args.time_key] = np.asarray(data[args.time_key])
        return bundle, "npz", []


def _load_csv_bundle(path: Path, args: argparse.Namespace) -> tuple[list[dict[str, Any]], str, list[str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            return [], "csv", ["CSV header is missing"]
        required = [
            args.lambda2_col,
            args.g12_col,
            args.b_col,
            args.pressure_hessian_col,
            *args.index_cols,
        ]
        if args.beta_value is None:
            required.append(args.beta_col)
        missing = [name for name in required if name not in reader.fieldnames]
        rows = list(reader)
        if missing:
            return rows, "csv", missing
        return rows, "csv", []


def _connected_components_3d(mask: np.ndarray) -> int:
    if mask.ndim != 3:
        raise ValueError(f"connected-component count requires a 3D mask, got shape {mask.shape!r}")

    active = np.asarray(mask, dtype=bool)
    if not np.any(active):
        return 0

    visited = np.zeros(active.shape, dtype=bool)
    nx, ny, nz = active.shape
    count = 0

    for start in np.argwhere(active):
        x, y, z = (int(start[0]), int(start[1]), int(start[2]))
        if visited[x, y, z]:
            continue

        count += 1
        stack = [(x, y, z)]
        visited[x, y, z] = True

        while stack:
            cx, cy, cz = stack.pop()
            neighbors = (
                (cx - 1, cy, cz),
                (cx + 1, cy, cz),
                (cx, cy - 1, cz),
                (cx, cy + 1, cz),
                (cx, cy, cz - 1),
                (cx, cy, cz + 1),
            )
            for nx_i, ny_i, nz_i in neighbors:
                if nx_i < 0 or ny_i < 0 or nz_i < 0:
                    continue
                if nx_i >= nx or ny_i >= ny or nz_i >= nz:
                    continue
                if active[nx_i, ny_i, nz_i] and not visited[nx_i, ny_i, nz_i]:
                    visited[nx_i, ny_i, nz_i] = True
                    stack.append((nx_i, ny_i, nz_i))

    return count


def _slice_time_labels(times: np.ndarray | None, n_slices: int) -> list[tuple[str, float | None]]:
    if times is None:
        return [(f"slice_{idx}", None) for idx in range(n_slices)]

    time_array = np.asarray(times)
    if time_array.ndim == 0:
        scalar = _as_float(time_array)
        return [(f"slice_{idx}", scalar) for idx in range(n_slices)]
    if time_array.ndim != 1:
        raise ValueError(f"time must be scalar or 1D, got shape {time_array.shape!r}")
    if len(time_array) != n_slices:
        raise ValueError(
            f"time length {len(time_array)} does not match number of slices {n_slices}"
        )
    labels: list[tuple[str, float | None]] = []
    for idx, value in enumerate(time_array):
        labels.append((f"t={_as_float(value):.12g}", _as_float(value)))
    return labels


def _beta_for_slice(beta: np.ndarray | None, beta_value: float | None, slice_index: int, n_slices: int) -> tuple[float, str]:
    if beta_value is not None:
        return float(beta_value), "cli-beta-value"

    if beta is None:
        raise ValueError("Betti-0 requires beta(t) data or --beta-value; no beta source was supplied")

    beta_array = np.asarray(beta)
    if beta_array.ndim == 0:
        return _as_float(beta_array), "input-beta-scalar"
    if beta_array.ndim != 1:
        raise ValueError(f"beta must be scalar or 1D, got shape {beta_array.shape!r}")
    if len(beta_array) != n_slices:
        raise ValueError(
            f"beta length {len(beta_array)} does not match number of slices {n_slices}"
        )
    return _as_float(beta_array[slice_index]), "input-beta-series"


def _evaluate_slice(
    *,
    lambda2: np.ndarray,
    g12: np.ndarray,
    b_field: np.ndarray,
    pressure_hessian_norm: np.ndarray,
    lambda2_band: float,
    beta: float,
) -> tuple[dict[str, Any], list[str]]:
    errors: list[str] = []

    if lambda2.shape != g12.shape or lambda2.shape != b_field.shape or lambda2.shape != pressure_hessian_norm.shape:
        errors.append(
            "field shapes do not match: "
            f"lambda2={lambda2.shape!r}, g12={g12.shape!r}, "
            f"B_k={b_field.shape!r}, pressure_hessian_norm={pressure_hessian_norm.shape!r}"
        )
        return {}, errors
    if lambda2.ndim != 3:
        errors.append(f"supported DNS layout is 3D per slice; got shape {lambda2.shape!r}")
        return {}, errors

    finite = (
        np.isfinite(lambda2)
        & np.isfinite(g12)
        & np.isfinite(b_field)
        & np.isfinite(pressure_hessian_norm)
    )
    boundary_mask = finite & (np.abs(lambda2) <= lambda2_band)
    boundary_cells = int(np.count_nonzero(boundary_mask))
    if boundary_cells == 0:
        errors.append(
            f"boundary layer |lambda2| <= {lambda2_band:g} is empty; cannot compute min g12 or rho"
        )
        return {}, errors

    boundary_g12 = np.asarray(g12[boundary_mask], dtype=float)
    boundary_pressure_hessian = np.asarray(pressure_hessian_norm[boundary_mask], dtype=float)
    if np.any(boundary_pressure_hessian < 0.0):
        errors.append("pressure_hessian_norm must be nonnegative on the boundary layer")
        return {}, errors

    boundary_denominator = 1.0 + boundary_pressure_hessian
    if np.any(boundary_denominator <= 0.0) or not np.all(np.isfinite(boundary_denominator)):
        errors.append("rho denominator 1 + pressure_hessian_norm is invalid on the boundary layer")
        return {}, errors

    boundary_rho = np.asarray(b_field[boundary_mask], dtype=float) / boundary_denominator
    threshold_mask = finite & (lambda2 <= beta)
    betti0 = _connected_components_3d(threshold_mask)

    return {
        "boundary_cells": boundary_cells,
        "min_g12_boundary": float(np.min(boundary_g12)),
        "rho_min_boundary": float(np.min(boundary_rho)),
        "rho_mean_boundary": float(np.mean(boundary_rho)),
        "rho_max_boundary": float(np.max(boundary_rho)),
        "betti0": int(betti0),
        "beta_value": float(beta),
    }, errors


def _evaluate_npz(path: Path, args: argparse.Namespace) -> FileDiagnostics:
    bundle, fmt, missing = _load_npz_bundle(path, args)
    if missing:
        return FileDiagnostics(
            path=str(path),
            format=fmt,
            status="missing-required-keys",
            boundary_band=float(args.lambda2_band),
            beta_source="unavailable",
            slices=[],
            missing_files=[],
            missing_columns=missing,
            errors=[],
        )

    lambda2 = np.asarray(bundle[args.lambda2_key])
    g12 = np.asarray(bundle[args.g12_key])
    b_field = np.asarray(bundle[args.b_key])
    pressure_hessian_norm = np.asarray(bundle[args.pressure_hessian_key])
    beta = bundle.get(args.beta_key)
    times = bundle.get(args.time_key)

    try:
        n_slices = 1 if lambda2.ndim == 3 else lambda2.shape[0]
        if lambda2.ndim not in {3, 4}:
            raise ValueError(f"lambda2 must be 3D or 4D, got shape {lambda2.shape!r}")
        if lambda2.shape != g12.shape or lambda2.shape != b_field.shape or lambda2.shape != pressure_hessian_norm.shape:
            raise ValueError(
                "npz field shapes must match exactly: "
                f"lambda2={lambda2.shape!r}, g12={g12.shape!r}, "
                f"B_k={b_field.shape!r}, pressure_hessian_norm={pressure_hessian_norm.shape!r}"
            )

        if lambda2.ndim == 3:
            field_slices = [(0, lambda2, g12, b_field, pressure_hessian_norm)]
        else:
            field_slices = [
                (idx, lambda2[idx], g12[idx], b_field[idx], pressure_hessian_norm[idx])
                for idx in range(lambda2.shape[0])
            ]

        labels = _slice_time_labels(times, n_slices)
        slices: list[SliceDiagnostics] = []
        errors: list[str] = []
        beta_source = "unavailable"
        for idx, lambda2_slice, g12_slice, b_slice, h_slice in field_slices:
            beta_value, beta_source = _beta_for_slice(beta, args.beta_value, idx, n_slices)
            summary, slice_errors = _evaluate_slice(
                lambda2=lambda2_slice,
                g12=g12_slice,
                b_field=b_slice,
                pressure_hessian_norm=h_slice,
                lambda2_band=float(args.lambda2_band),
                beta=beta_value,
            )
            errors.extend(slice_errors)
            time_label, time_value = labels[idx]
            if summary:
                slices.append(
                    SliceDiagnostics(
                        slice_index=idx,
                        time_label=time_label,
                        time_value=time_value,
                        boundary_cells=int(summary["boundary_cells"]),
                        min_g12_boundary=float(summary["min_g12_boundary"]),
                        rho_min_boundary=float(summary["rho_min_boundary"]),
                        rho_mean_boundary=float(summary["rho_mean_boundary"]),
                        rho_max_boundary=float(summary["rho_max_boundary"]),
                        betti0=int(summary["betti0"]),
                        beta_value=float(summary["beta_value"]),
                    )
                )

        status = "ok" if not errors else "error"
        return FileDiagnostics(
            path=str(path),
            format=fmt,
            status=status,
            boundary_band=float(args.lambda2_band),
            beta_source=beta_source,
            slices=slices,
            missing_files=[],
            missing_columns=[],
            errors=errors,
        )
    except Exception as exc:
        return FileDiagnostics(
            path=str(path),
            format=fmt,
            status="error",
            boundary_band=float(args.lambda2_band),
            beta_source="unavailable",
            slices=[],
            missing_files=[],
            missing_columns=[],
            errors=[str(exc)],
        )


def _csv_group_rows(rows: list[dict[str, str]], time_col: str | None) -> list[tuple[str, float | None, list[dict[str, str]]]]:
    if time_col is None:
        return [("slice_0", None, rows)]

    groups: list[tuple[str, float | None, list[dict[str, str]]]] = []
    seen: dict[str, list[dict[str, str]]] = {}
    order: list[str] = []
    for row in rows:
        raw = row[time_col]
        if raw not in seen:
            seen[raw] = []
            order.append(raw)
        seen[raw].append(row)

    for raw in order:
        try:
            time_value = float(raw)
        except ValueError:
            time_value = None
        groups.append((f"t={raw}", time_value, seen[raw]))
    return groups


def _csv_grid_from_rows(
    rows: list[dict[str, str]],
    args: argparse.Namespace,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, float | None, str, list[str]]:
    missing: list[str] = []
    required = [args.lambda2_col, args.g12_col, args.b_col, args.pressure_hessian_col, *args.index_cols]
    fieldnames = set(rows[0].keys()) if rows else set()
    missing.extend([name for name in required if name not in fieldnames])
    if missing:
        return np.empty((0, 0, 0)), np.empty((0, 0, 0)), np.empty((0, 0, 0)), np.empty((0, 0, 0)), None, "csv", missing

    index_cols = list(args.index_cols)
    x_values: list[int] = []
    y_values: list[int] = []
    z_values: list[int] = []
    parsed_rows: list[tuple[int, int, int, float, float, float, float]] = []
    beta_values: list[float] = []
    beta_present = args.beta_col in fieldnames

    for row in rows:
        x = _parse_index(row[index_cols[0]], index_cols[0])
        y = _parse_index(row[index_cols[1]], index_cols[1])
        z = _parse_index(row[index_cols[2]], index_cols[2])
        l2 = float(row[args.lambda2_col])
        g12 = float(row[args.g12_col])
        b = float(row[args.b_col])
        h = float(row[args.pressure_hessian_col])
        parsed_rows.append((x, y, z, l2, g12, b, h))
        x_values.append(x)
        y_values.append(y)
        z_values.append(z)
        if beta_present:
            beta_values.append(float(row[args.beta_col]))

    xs = _sorted_unique(x_values)
    ys = _sorted_unique(y_values)
    zs = _sorted_unique(z_values)
    shape = (len(xs), len(ys), len(zs))
    l2_field = np.full(shape, np.nan, dtype=float)
    g12_field = np.full(shape, np.nan, dtype=float)
    b_field = np.full(shape, np.nan, dtype=float)
    h_field = np.full(shape, np.nan, dtype=float)
    xi = {value: idx for idx, value in enumerate(xs)}
    yi = {value: idx for idx, value in enumerate(ys)}
    zi = {value: idx for idx, value in enumerate(zs)}

    for row in parsed_rows:
        x, y, z, l2, g12, b, h = row
        idx = (xi[x], yi[y], zi[z])
        if not np.isnan(l2_field[idx]):
            raise ValueError(f"duplicate CSV row for grid index {idx!r}")
        l2_field[idx] = l2
        g12_field[idx] = g12
        b_field[idx] = b
        h_field[idx] = h

    if beta_present:
        beta_unique = sorted(set(beta_values))
        if len(beta_unique) != 1:
            raise ValueError("CSV beta column must be constant within a single slice")
        beta_scalar = float(beta_unique[0])
    else:
        beta_scalar = None

    if np.any(np.isnan(l2_field)) or np.any(np.isnan(g12_field)) or np.any(np.isnan(b_field)) or np.any(np.isnan(h_field)):
        raise ValueError("CSV grid is missing one or more required tensor cells")

    return l2_field, g12_field, b_field, h_field, beta_scalar, "csv", []


def _evaluate_csv(path: Path, args: argparse.Namespace) -> FileDiagnostics:
    rows, fmt, missing = _load_csv_bundle(path, args)
    if missing:
        return FileDiagnostics(
            path=str(path),
            format=fmt,
            status="missing-required-columns",
            boundary_band=float(args.lambda2_band),
            beta_source="unavailable",
            slices=[],
            missing_files=[],
            missing_columns=missing,
            errors=[],
        )
    if not rows:
        return FileDiagnostics(
            path=str(path),
            format=fmt,
            status="empty",
            boundary_band=float(args.lambda2_band),
            beta_source="unavailable",
            slices=[],
            missing_files=[],
            missing_columns=[],
            errors=["CSV file contains no rows"],
        )

    time_col = args.time_col if rows and args.time_col in rows[0] else None
    groups = _csv_group_rows(rows, time_col)
    slices: list[SliceDiagnostics] = []
    errors: list[str] = []
    beta_source = "unavailable"

    for idx, (time_label, time_value, group_rows) in enumerate(groups):
        try:
            l2_field, g12_field, b_field, h_field, beta_field, _, _ = _csv_grid_from_rows(group_rows, args)
            beta_value, beta_source = _beta_for_slice(beta_field, args.beta_value, idx, len(groups))
            summary, slice_errors = _evaluate_slice(
                lambda2=l2_field,
                g12=g12_field,
                b_field=b_field,
                pressure_hessian_norm=h_field,
                lambda2_band=float(args.lambda2_band),
                beta=beta_value,
            )
            errors.extend(slice_errors)
            if summary:
                slices.append(
                    SliceDiagnostics(
                        slice_index=idx,
                        time_label=time_label,
                        time_value=time_value,
                        boundary_cells=int(summary["boundary_cells"]),
                        min_g12_boundary=float(summary["min_g12_boundary"]),
                        rho_min_boundary=float(summary["rho_min_boundary"]),
                        rho_mean_boundary=float(summary["rho_mean_boundary"]),
                        rho_max_boundary=float(summary["rho_max_boundary"]),
                        betti0=int(summary["betti0"]),
                        beta_value=float(summary["beta_value"]),
                    )
                )
        except Exception as exc:
            errors.append(f"{path}: {exc}")

    status = "ok" if not errors else "error"
    return FileDiagnostics(
        path=str(path),
        format=fmt,
        status=status,
        boundary_band=float(args.lambda2_band),
        beta_source=beta_source,
        slices=slices,
        missing_files=[],
        missing_columns=[],
        errors=errors,
    )


def _load_input_path(path: Path, args: argparse.Namespace) -> list[FileDiagnostics]:
    if not path.exists():
        return [
            FileDiagnostics(
                path=str(path),
                format="missing",
                status="missing-file",
                boundary_band=float(args.lambda2_band),
                beta_source="unavailable",
                slices=[],
                missing_files=[str(path)],
                missing_columns=[],
                errors=[],
            )
        ]

    if path.is_dir():
        candidates = sorted(p for p in path.rglob("*") if p.is_file() and _is_supported_file(p))
        if not candidates:
            return [
                FileDiagnostics(
                    path=str(path),
                    format="directory",
                    status="missing-supported-files",
                    boundary_band=float(args.lambda2_band),
                    beta_source="unavailable",
                    slices=[],
                    missing_files=[f"{path}: no .npz or .csv inputs found"],
                    missing_columns=[],
                    errors=[],
                )
            ]
        out: list[FileDiagnostics] = []
        for candidate in candidates:
            out.extend(_load_input_path(candidate, args))
        return out

    suffix = path.suffix.lower()
    if suffix == ".npz":
        return [_evaluate_npz(path, args)]
    if suffix == ".csv":
        return [_evaluate_csv(path, args)]
    return [
        FileDiagnostics(
            path=str(path),
            format="unsupported",
            status="unsupported-file-type",
            boundary_band=float(args.lambda2_band),
            beta_source="unavailable",
            slices=[],
            missing_files=[],
            missing_columns=[],
            errors=[f"unsupported file type {path.suffix!r}; expected .npz or .csv"],
        )
    ]


def _summarize(diagnostics: list[FileDiagnostics], args: argparse.Namespace) -> dict[str, Any]:
    errors = [error for item in diagnostics for error in item.errors]
    missing_files = [missing for item in diagnostics for missing in item.missing_files]
    missing_columns = [column for item in diagnostics for column in item.missing_columns]
    all_slices = [asdict(slice_item) for item in diagnostics for slice_item in item.slices]

    min_g12_values = [slice_item["min_g12_boundary"] for slice_item in all_slices if slice_item["min_g12_boundary"] is not None]
    rho_min_values = [slice_item["rho_min_boundary"] for slice_item in all_slices if slice_item["rho_min_boundary"] is not None]
    rho_mean_values = [slice_item["rho_mean_boundary"] for slice_item in all_slices if slice_item["rho_mean_boundary"] is not None]
    rho_max_values = [slice_item["rho_max_boundary"] for slice_item in all_slices if slice_item["rho_max_boundary"] is not None]
    betti0_values = [slice_item["betti0"] for slice_item in all_slices if slice_item["betti0"] is not None]

    status = "ok" if not errors and not missing_files and not missing_columns else "error"
    return {
        "status": status,
        "contract": _contract_summary(args),
        "files": [asdict(item) for item in diagnostics],
        "all_slices": all_slices,
        "aggregate": {
            "min_g12_boundary": min(min_g12_values) if min_g12_values else None,
            "rho_min_boundary": min(rho_min_values) if rho_min_values else None,
            "rho_mean_boundary": float(np.mean(rho_mean_values)) if rho_mean_values else None,
            "rho_max_boundary": max(rho_max_values) if rho_max_values else None,
            "betti0_max": max(betti0_values) if betti0_values else None,
            "betti0_sum": int(sum(betti0_values)) if betti0_values else None,
        },
        "errors": errors,
        "missing_files": missing_files,
        "missing_columns": missing_columns,
    }


def _render_text(summary: dict[str, Any], args: argparse.Namespace) -> str:
    lines = [
        "ns_boundary_preflight_diagnostic",
        f"status: {summary['status']}",
        f"strict: {args.strict}",
        f"lambda2_band: {args.lambda2_band:g}",
    ]
    contract = summary["contract"]
    lines.append("input_contract:")
    lines.append(f"  min_g12: required={', '.join(contract['min_g12']['required'])}; {contract['min_g12']['meaning']}")
    lines.append(f"  rho: required={', '.join(contract['rho']['required'])}; {contract['rho']['meaning']}")
    lines.append(f"  betti0: required={', '.join(contract['betti0']['required'])}; {contract['betti0']['meaning']}")
    aggregate = summary["aggregate"]
    lines.append(f"aggregate.min_g12_boundary: {aggregate['min_g12_boundary']}")
    lines.append(f"aggregate.rho_min_boundary: {aggregate['rho_min_boundary']}")
    lines.append(f"aggregate.rho_mean_boundary: {aggregate['rho_mean_boundary']}")
    lines.append(f"aggregate.rho_max_boundary: {aggregate['rho_max_boundary']}")
    lines.append(f"aggregate.betti0_max: {aggregate['betti0_max']}")
    lines.append(f"aggregate.betti0_sum: {aggregate['betti0_sum']}")

    for item in summary["files"]:
        lines.append(f"file: {item['path']}")
        lines.append(f"  format: {item['format']}")
        lines.append(f"  status: {item['status']}")
        lines.append(f"  beta_source: {item['beta_source']}")
        for slice_item in item["slices"]:
            lines.append(
                "  "
                + f"{slice_item['time_label']}: boundary_cells={slice_item['boundary_cells']}, "
                + f"min_g12={slice_item['min_g12_boundary']}, "
                + f"rho_min={slice_item['rho_min_boundary']}, "
                + f"rho_mean={slice_item['rho_mean_boundary']}, "
                + f"rho_max={slice_item['rho_max_boundary']}, "
                + f"betti0={slice_item['betti0']}, beta={slice_item['beta_value']}"
            )
        for error in item["errors"]:
            lines.append(f"  error: {error}")

    if summary["missing_files"]:
        lines.append("missing_files:")
        for entry in summary["missing_files"]:
            lines.append(f"  - {entry}")
    if summary["missing_columns"]:
        lines.append("missing_columns:")
        for entry in summary["missing_columns"]:
            lines.append(f"  - {entry}")
    if summary["errors"]:
        lines.append("errors:")
        for entry in summary["errors"]:
            lines.append(f"  - {entry}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="\n".join(_input_contract_lines()),
    )
    parser.add_argument(
        "--input",
        action="append",
        default=[],
        help=(
            "Raw DNS tensor input file or directory. May be repeated. "
            "Required contract: lambda2/g12 for min_g12, lambda2/B_k/pressure_hessian_norm for rho, "
            "and lambda2 plus beta(t) or --beta-value for Betti-0."
        ),
    )
    parser.add_argument("--lambda2-band", type=float, default=DEFAULT_LAMBDA2_BAND)
    parser.add_argument(
        "--beta-value",
        type=float,
        default=None,
        help="Override beta(t) with a scalar threshold; required if the archive does not provide beta data.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of text.")
    parser.add_argument("--strict", action="store_true", default=True)
    parser.add_argument("--lenient", action="store_true", help="Do not exit nonzero on validation failures.")
    parser.add_argument("--time-key", default=DEFAULT_TIME_COL)
    parser.add_argument("--time-col", default=DEFAULT_TIME_COL)
    parser.add_argument("--index-cols", nargs=3, default=list(DEFAULT_INDEX_COLS))
    parser.add_argument("--lambda2-key", default=DEFAULT_LAMBDA2_KEY)
    parser.add_argument("--g12-key", default=DEFAULT_G12_KEY)
    parser.add_argument("--b-key", default=DEFAULT_B_KEY)
    parser.add_argument("--pressure-hessian-key", default=DEFAULT_PRESSURE_HESSIAN_KEY)
    parser.add_argument("--beta-key", default=DEFAULT_BETA_KEY)
    parser.add_argument("--lambda2-col", default=DEFAULT_LAMBDA2_KEY)
    parser.add_argument("--g12-col", default=DEFAULT_G12_KEY)
    parser.add_argument("--b-col", default=DEFAULT_B_KEY)
    parser.add_argument("--pressure-hessian-col", default=DEFAULT_PRESSURE_HESSIAN_KEY)
    parser.add_argument("--beta-col", default=DEFAULT_BETA_KEY)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    args.index_cols = tuple(args.index_cols)

    if not args.input:
        summary = {
            "status": "error",
            "contract": _contract_summary(args),
            "files": [],
            "all_slices": [],
            "aggregate": {
                "min_g12_boundary": None,
                "rho_min_boundary": None,
                "rho_mean_boundary": None,
                "rho_max_boundary": None,
                "betti0_max": None,
                "betti0_sum": None,
            },
            "errors": ["no input files supplied"],
            "missing_files": ["<no input files supplied>"],
            "missing_columns": [],
        }
        text = json.dumps(summary, sort_keys=True, separators=(",", ":")) if args.json else _render_text(summary, args)
        print(text)
        raise SystemExit(2 if not args.lenient else 0)

    diagnostics: list[FileDiagnostics] = []
    for input_arg in args.input:
        diagnostics.extend(_load_input_path(Path(input_arg), args))

    summary = _summarize(diagnostics, args)
    text = json.dumps(summary, sort_keys=True, separators=(",", ":")) if args.json else _render_text(summary, args)
    print(text)

    if summary["status"] != "ok" and not args.lenient and args.strict:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
