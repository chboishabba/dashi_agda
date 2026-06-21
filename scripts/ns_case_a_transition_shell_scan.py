#!/usr/bin/env python3
"""Empirical Case A transition shell scan on the raw N128 archive.

This scan is fail-closed and non-promoting. It reconstructs the strain tensor
from raw velocity snapshots, uses narrow |lambda2| bands to locate boundary
proxies for the lambda2=0 transition, and measures the geometry of
high-strain sets

    A_K0 = { ||S||_F > K0 and lambda2 >= 0 }

relative to that proxy. The output is per-frame plus aggregate telemetry only;
no theorem, Clay, or promotion claim is made.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy.ndimage import grey_dilation as scipy_grey_dilation


SCRIPT_NAME = "scripts/ns_case_a_transition_shell_scan.py"
CONTRACT = "ns_case_a_transition_shell_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_CASE_A_TRANSITION_SHELL_SCAN"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_case_a_transition_shell_scan_N128_20260621.json"
)

DEFAULT_FRAME_LIMIT = 13
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_LAMBDA2_BANDS = (1.0e-4, 5.0e-4, 1.0e-3, 5.0e-3)
DEFAULT_STRAIN_THRESHOLDS = (0.0, 0.25, 0.5, 1.0, 2.0, 4.0)
DEFAULT_SHELL_STEP_LIMIT = 8

CONTROL_CARD = {
    "O": "Empirical Case A transition-shell scan on the raw N128 archive.",
    "R": (
        "Reconstruct strain from raw velocity, locate narrow lambda2 boundary proxies, and "
        "measure high-strain set A_K0 geometry against the proxy."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed empirical telemetry only: malformed inputs, non-finite reconstruction, or schema gaps become explicit errors.",
    "L": "Load raw archive, reconstruct strain/lambda2, sweep K0 thresholds and lambda2 proxy bands, and emit per-frame plus aggregate telemetry.",
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion claim is inferred by this scan.",
    "F": "The lambda2=0 transition is only approximated numerically by narrow |lambda2| shells; the output is empirical only.",
}

BENIGN_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback 6.283185307179586",
)


@dataclass(frozen=True)
class RawBundle:
    path: Path
    u: np.ndarray
    v: np.ndarray
    w: np.ndarray
    has_frame_axis: bool
    frame_count: int
    domain_length: float
    grid_spacing: float


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be nonnegative")
    return parsed


def _positive_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed <= 0.0:
        raise argparse.ArgumentTypeError("value must be finite and positive")
    return parsed


def _nonnegative_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError("value must be finite and nonnegative")
    return parsed


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


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


def _is_benign_warning(value: str) -> bool:
    if not isinstance(value, str):
        return False
    return any(value.endswith(suffix) or value == suffix for suffix in BENIGN_WARNING_SUFFIXES)


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    if not path.exists():
        raise FileNotFoundError(f"archive missing: {path}")
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}
    if "meta_json" in payload:
        try:
            metadata = json.loads(str(np.asarray(payload["meta_json"]).item()))
        except Exception:
            metadata = None
        else:
            if isinstance(metadata, dict):
                for key in ("grid_spacing", "dx", "dh", "domain_length", "length", "L", "domain", "N", "N1", "N2", "N3"):
                    if key in metadata and key not in payload:
                        try:
                            payload[key] = np.asarray(metadata[key])
                        except Exception:
                            pass
    return payload


def _read_scalar_metadata(data: dict[str, np.ndarray], names: tuple[str, ...]) -> tuple[float | None, str | None]:
    for name in names:
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.shape == ():
            scalar = value.item()
        elif value.ndim == 0:
            scalar = value.reshape(()).item()
        elif value.ndim == 1 and value.size == 1:
            scalar = value.reshape(-1)[0].item()
        else:
            continue
        if isinstance(scalar, (bytes, bytearray, np.bytes_)):
            scalar = bytes(scalar).decode("utf-8")
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        try:
            return float(scalar), name
        except Exception:
            continue
    return None, None


def _coerce_float(value: Any, *, name: str | None = None) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name or 'value'} must be finite")
    return parsed


def _infer_domain_length(data: dict[str, np.ndarray], n: int, warnings: list[str]) -> float:
    domain_length, domain_key = _read_scalar_metadata(data, ("domain_length", "length", "L", "domain"))
    if domain_length is not None:
        domain_value = _coerce_float(domain_length, name=domain_key or "domain_length")
        if domain_value <= 0.0:
            raise ValueError("domain_length must be positive")
    else:
        domain_value = None

    spacing, spacing_key = _read_scalar_metadata(data, ("grid_spacing", "dx", "dh"))
    if spacing is not None:
        spacing_value = _coerce_float(spacing, name=spacing_key or "grid_spacing")
        if spacing_value <= 0.0:
            raise ValueError("grid_spacing must be positive")
        if domain_value is None:
            domain_value = float(spacing_value * n)
        elif not math.isclose(domain_value, spacing_value * n, rel_tol=1.0e-8, abs_tol=1.0e-8):
            warnings.append(
                f"domain_length/grid_spacing mismatch: {domain_value} vs {spacing_value * n} (using domain_length)"
            )

    if domain_value is not None:
        return domain_value

    fallback = 2.0 * math.pi
    warnings.append(f"domain_length unavailable; using fallback {fallback}")
    return fallback


def _select_velocity_components(data: dict[str, np.ndarray], warnings: list[str]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if "velocity_snapshots" in data:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        if velocity.ndim == 5 and velocity.shape[1] == 3 and velocity.shape[-1] != 3:
            warnings.append("velocity_snapshots axis-1 channel layout detected")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots trailing channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        if velocity.ndim == 4 and velocity.shape[-1] == 3:
            warnings.append("velocity_snapshots last-axis layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"unsupported velocity_snapshots shape {velocity.shape!r}")

    if {"u", "v", "w"}.issubset(data):
        return (
            np.asarray(data["u"], dtype=np.float64),
            np.asarray(data["v"], dtype=np.float64),
            np.asarray(data["w"], dtype=np.float64),
        )

    if "velocity" in data:
        velocity = np.asarray(data["velocity"], dtype=np.float64)
        if velocity.ndim == 4 and velocity.shape[1] == 3:
            warnings.append("velocity axis-1 channel layout detected")
            return (
                np.asarray(velocity[:, 0], dtype=np.float64),
                np.asarray(velocity[:, 1], dtype=np.float64),
                np.asarray(velocity[:, 2], dtype=np.float64),
            )
        if velocity.ndim == 5 and velocity.shape[-1] == 3:
            warnings.append("velocity trailing channel layout detected")
            return (
                np.asarray(velocity[..., 0], dtype=np.float64),
                np.asarray(velocity[..., 1], dtype=np.float64),
                np.asarray(velocity[..., 2], dtype=np.float64),
            )
        raise ValueError(f"unsupported fallback velocity shape {velocity.shape!r}")

    raise ValueError("no raw velocity components found")


def _load_raw_bundle(path: Path, warnings: list[str]) -> RawBundle:
    data = _load_npz(path)
    u, v, w = _select_velocity_components(data, warnings)

    if u.ndim == 4 and v.ndim == 4 and w.ndim == 4:
        if int(u.shape[1]) == int(u.shape[2]) == int(u.shape[3]):
            has_frame_axis = True
            frame_count = int(u.shape[0])
        elif int(u.shape[0]) == 1 and int(u.shape[1]) == int(u.shape[2]) == int(u.shape[3]):
            has_frame_axis = False
            frame_count = 1
            u = np.asarray(u[0], dtype=np.float64)
            v = np.asarray(v[0], dtype=np.float64)
            w = np.asarray(w[0], dtype=np.float64)
        else:
            raise ValueError(f"unsupported 4D velocity shape {u.shape!r}")
    elif u.ndim == 3 and v.ndim == 3 and w.ndim == 3:
        has_frame_axis = False
        frame_count = 1
    else:
        raise ValueError(f"unsupported velocity rank combination {u.shape!r}")

    if has_frame_axis:
        n = int(u.shape[1])
        if not (u.shape[1] == u.shape[2] == u.shape[3]):
            raise ValueError(f"velocity snapshot shape not cubic: {u.shape!r}")
    else:
        n = int(u.shape[0])
        if not (u.shape[0] == u.shape[1] == u.shape[2]):
            raise ValueError(f"velocity component shape not cubic: {u.shape!r}")
    if n <= 1:
        raise ValueError(f"invalid grid size n={n}")

    if not np.all(np.isfinite(u)) or not np.all(np.isfinite(v)) or not np.all(np.isfinite(w)):
        raise ValueError(f"raw velocity contains non-finite values in {path}")

    domain_length = _infer_domain_length(data, n, warnings)
    grid_spacing = float(domain_length / float(n))
    return RawBundle(
        path=path,
        u=u,
        v=v,
        w=w,
        has_frame_axis=has_frame_axis,
        frame_count=frame_count,
        domain_length=domain_length,
        grid_spacing=grid_spacing,
    )


def _raw_velocity_frame(bundle: RawBundle, snapshot: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if not bundle.has_frame_axis:
        if snapshot != 0:
            raise ValueError(f"raw archive has no frame axis; requested snapshot {snapshot}")
        return (
            np.asarray(bundle.u, dtype=np.float64),
            np.asarray(bundle.v, dtype=np.float64),
            np.asarray(bundle.w, dtype=np.float64),
        )

    if snapshot < 0 or snapshot >= int(bundle.frame_count):
        raise ValueError(f"requested snapshot {snapshot} is out of range for {bundle.frame_count} frames")
    return (
        np.asarray(bundle.u, dtype=np.float64)[snapshot],
        np.asarray(bundle.v, dtype=np.float64)[snapshot],
        np.asarray(bundle.w, dtype=np.float64)[snapshot],
    )


def _spectral_derivative(field: np.ndarray, axis: int, domain_length: float) -> np.ndarray:
    n = int(field.shape[axis])
    frequencies = 2.0 * np.pi * np.fft.fftfreq(n, d=domain_length / float(n))
    reshape = [1, 1, 1]
    reshape[axis] = n
    factor = frequencies.reshape(reshape)
    transformed = np.fft.fftn(field, axes=(0, 1, 2))
    return np.fft.ifftn(1j * factor * transformed, axes=(0, 1, 2)).real


def _velocity_gradient(u: np.ndarray, v: np.ndarray, w: np.ndarray, domain_length: float) -> np.ndarray:
    grad = np.empty((3, 3) + u.shape, dtype=np.float64)
    for component_index, component in enumerate((u, v, w)):
        for axis in range(3):
            grad[component_index, axis] = _spectral_derivative(component, axis, domain_length)
    return grad


def _strain_tensor(grad: np.ndarray) -> np.ndarray:
    tensor = np.asarray(grad, dtype=np.float64)
    return 0.5 * (tensor + np.swapaxes(tensor, 0, 1))


def _strain_and_lambda2_from_velocity(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    grad = _velocity_gradient(u, v, w, domain_length)
    strain = _strain_tensor(grad)
    matrices = np.moveaxis(strain, (0, 1), (-2, -1))
    eigenvalues, _ = np.linalg.eigh(matrices)
    lambda2 = np.asarray(eigenvalues[..., 1], dtype=np.float64)
    strain_frobenius_sq = np.sum(strain * strain, axis=(0, 1))
    strain_frobenius = np.sqrt(np.maximum(strain_frobenius_sq, 0.0))
    return strain, strain_frobenius, lambda2


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _to_threshold_key(value: float) -> float:
    return float(f"{float(value):.12g}")


def _sorted_unique_floats(values: list[float], *, positive_only: bool, allow_zero: bool) -> list[float]:
    parsed: list[float] = []
    seen: set[float] = set()
    for raw in values:
        if not math.isfinite(raw):
            continue
        value = float(raw)
        if positive_only:
            if value <= 0.0:
                continue
        elif not allow_zero and value < 0.0:
            continue
        if value in seen:
            continue
        seen.add(value)
        parsed.append(value)
    parsed.sort()
    return parsed


def _threshold_bucket_counts(step_assignments: np.ndarray, high_mask: np.ndarray, shell_step_limit: int) -> tuple[list[int], list[float]]:
    if not np.any(high_mask):
        counts = [0] * (shell_step_limit + 2)
        return counts, [0.0] * (shell_step_limit + 2)
    clipped = np.asarray(step_assignments[high_mask], dtype=np.int64)
    clipped = np.where(clipped < 0, shell_step_limit + 1, clipped)
    clipped = np.clip(clipped, 0, shell_step_limit + 1)
    counts = np.bincount(clipped, minlength=shell_step_limit + 2).astype(int).tolist()
    total = int(np.sum(counts))
    fractions = [0.0 if total <= 0 else float(count) / float(total) for count in counts]
    return counts, fractions


def _shell_distance_stats(counts: list[int], dx: float) -> tuple[int | None, float | None, float | None, int | None, float | None, float | None, float | None]:
    total = int(sum(counts))
    if total <= 0:
        return None, None, None, None, None, None, None

    first = next((index for index, count in enumerate(counts) if count > 0), None)
    last = next((index for index in range(len(counts) - 1, -1, -1) if counts[index] > 0), None)
    weighted_sum = sum(index * count for index, count in enumerate(counts))
    mean_step = float(weighted_sum) / float(total)

    cumulative = 0
    median_bucket = None
    midpoint = (total - 1) // 2
    for index, count in enumerate(counts):
        cumulative += count
        if cumulative > midpoint:
            median_bucket = index
            break
    if median_bucket is None:
        median_bucket = len(counts) - 1

    return (
        first,
        mean_step,
        float(median_bucket),
        last,
        float(first) * dx if first is not None else None,
        mean_step * dx,
        float(median_bucket) * dx,
        float(last) * dx if last is not None else None,
    )


def _periodic_shell_assignments(mask: np.ndarray, shell_step_limit: int) -> np.ndarray:
    assigned = np.full(mask.shape, -1, dtype=np.int16)
    assigned[mask] = 0
    current = np.asarray(mask, dtype=np.uint8)
    footprint = np.ones((3, 3, 3), dtype=bool)
    for step in range(1, shell_step_limit + 1):
        current = np.asarray(scipy_grey_dilation(current, footprint=footprint, mode="wrap"), dtype=np.uint8)
        reached = current > 0
        newly = reached & (assigned < 0)
        assigned[newly] = step
        if not np.any(assigned < 0):
            break
    return assigned


def _build_error_payload(args: argparse.Namespace, errors: list[str], warnings: list[str]) -> dict[str, Any]:
    thresholds = _sorted_unique_floats(list(args.strain_thresholds), positive_only=False, allow_zero=True)
    bands = _sorted_unique_floats(list(args.lambda2_band_values), positive_only=True, allow_zero=False)
    return {
        "contract": CONTRACT,
        "status": ERROR_STATUS,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        **CONTROL_CARD,
        "script": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "lambda2_band_values": bands,
            "strain_thresholds": thresholds,
            "shell_step_limit": int(args.shell_step_limit),
            "boundary_proxy_selection_policy": "narrowest_nonempty",
            "shell_metric": "periodic_26_neighborhood_steps",
        },
        "frames": [],
        "aggregate": {
            "processed_frames": 0,
            "ok_frames": 0,
            "partial_frames": 0,
            "missing_frames": 0,
            "error_frames": 1,
        },
        "warnings": warnings,
        "errors": errors,
        "changed_files": [str(args.output)],
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE, help="Raw N128 archive path")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="Frame index for 4D archives")
    parser.add_argument("--frame-limit", type=_positive_int, default=DEFAULT_FRAME_LIMIT, help="Maximum number of frames to process")
    parser.add_argument("--zero-eps", type=_nonnegative_float, default=DEFAULT_ZERO_EPS, help="Tolerance for zero classification")
    parser.add_argument(
        "--lambda2-band-values",
        type=_positive_float,
        nargs="+",
        default=list(DEFAULT_LAMBDA2_BANDS),
        help="Sorted lambda2 band candidates used to locate the boundary proxy",
    )
    parser.add_argument(
        "--strain-thresholds",
        type=_nonnegative_float,
        nargs="+",
        default=list(DEFAULT_STRAIN_THRESHOLDS),
        help="Nonnegative strain thresholds K0 used to define A_K0",
    )
    parser.add_argument(
        "--shell-step-limit",
        type=_positive_int,
        default=DEFAULT_SHELL_STEP_LIMIT,
        help="Maximum periodic shell depth used for distance estimates",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def _frame_status_summary(rows: list[dict[str, Any]]) -> dict[str, int]:
    counts = {"ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 0}
    for row in rows:
        status = row.get("status")
        if status == OK_STATUS:
            counts["ok_frames"] += 1
        elif status == PARTIAL_STATUS:
            counts["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            counts["missing_frames"] += 1
        else:
            counts["error_frames"] += 1
    return counts


def _build_aggregate(
    rows: list[dict[str, Any]],
    lambda2_band_values: list[float],
    strain_thresholds: list[float],
    shell_step_limit: int,
) -> dict[str, Any]:
    processed_frames = len(rows)
    status_counts = _frame_status_summary(rows)
    global_cell_count = sum(int(row.get("cell_count", 0)) for row in rows)
    global_finite_cell_count = sum(int(row.get("finite_cell_count", 0)) for row in rows)

    band_rows: list[dict[str, Any]] = []
    for band_index, band in enumerate(lambda2_band_values):
        count = 0
        selected_count = 0
        for row in rows:
            boundary_proxy = row.get("boundary_proxy")
            if not isinstance(boundary_proxy, dict):
                continue
            band_rows_local = boundary_proxy.get("band_rows")
            if not isinstance(band_rows_local, list) or band_index >= len(band_rows_local):
                continue
            count += int(band_rows_local[band_index].get("count", 0))
            if boundary_proxy.get("selected_band_index") == band_index:
                selected_count += 1
        band_rows.append(
            {
                "band": float(band),
                "count": int(count),
                "fraction": _fraction(int(count), global_finite_cell_count),
                "selected_count": int(selected_count),
                "selected_fraction": _fraction(int(selected_count), processed_frames),
            }
        )

    threshold_rows: list[dict[str, Any]] = []
    for threshold_index, threshold in enumerate(strain_thresholds):
        combined_counts = [0] * (shell_step_limit + 2)
        high_count = 0
        overlap_count = 0
        cumulative_distance_steps = 0.0
        cumulative_distance_physical = 0.0
        min_step: int | None = None
        max_step: int | None = None
        for row in rows:
            threshold_rows_data = row.get("threshold_rows", [])
            if threshold_index >= len(threshold_rows_data):
                continue
            item = threshold_rows_data[threshold_index]
            item_counts = [int(value) for value in item.get("shell_step_counts", [])]
            if len(item_counts) == len(combined_counts):
                combined_counts = [left + right for left, right in zip(combined_counts, item_counts)]
            high_count += int(item.get("high_strain_count", 0))
            overlap_count += int(item.get("high_strain_boundary_overlap_count", 0))
            if item.get("distance_step_mean") is not None:
                cumulative_distance_steps += float(item["distance_step_mean"]) * float(item.get("high_strain_count", 0))
                cumulative_distance_physical += float(item["distance_physical_mean"]) * float(item.get("high_strain_count", 0))
            if item.get("distance_step_min") is not None:
                value = int(item["distance_step_min"])
                min_step = value if min_step is None else min(min_step, value)
            if item.get("distance_step_max") is not None:
                value = int(item["distance_step_max"])
                max_step = value if max_step is None else max(max_step, value)

        if high_count > 0:
            mean_step = cumulative_distance_steps / float(high_count)
            mean_physical = cumulative_distance_physical / float(high_count)
            cumulative = 0
            median_step = 0
            midpoint = (high_count - 1) // 2
            for index, count in enumerate(combined_counts):
                cumulative += count
                if cumulative > midpoint:
                    median_step = index
                    break
            shell_fraction_within_limit = _fraction(sum(combined_counts[:-1]), high_count)
        else:
            mean_step = None
            mean_physical = None
            median_step = None
            shell_fraction_within_limit = 0.0

        threshold_rows.append(
            {
                "k0": float(threshold),
                "high_strain_count": int(high_count),
                "high_strain_fraction": _fraction(int(high_count), global_finite_cell_count),
                "high_strain_boundary_overlap_count": int(overlap_count),
                "high_strain_boundary_overlap_fraction": _fraction(int(overlap_count), high_count),
                "shell_step_limit": int(shell_step_limit),
                "shell_step_counts": [int(value) for value in combined_counts],
                "shell_step_fractions": [0.0 if high_count <= 0 else float(value) / float(high_count) for value in combined_counts],
                "shell_fraction_within_limit": float(shell_fraction_within_limit),
                "distance_step_min": min_step,
                "distance_step_mean": mean_step,
                "distance_step_median": median_step,
                "distance_step_max": max_step,
                "distance_physical_min": None if min_step is None else float(min_step),
                "distance_physical_mean": mean_physical,
                "distance_physical_median": None if median_step is None else float(median_step),
                "distance_physical_max": None if max_step is None else float(max_step),
            }
        )

    selected_band_mode = None
    if rows:
        band_counter: Counter[float] = Counter()
        for row in rows:
            boundary_proxy = row.get("boundary_proxy")
            if not isinstance(boundary_proxy, dict):
                continue
            selected_band = boundary_proxy.get("selected_band")
            if isinstance(selected_band, (int, float)) and math.isfinite(float(selected_band)):
                band_counter[float(selected_band)] += 1
        if band_counter:
            selected_band_mode = float(band_counter.most_common(1)[0][0])

    return {
        "processed_frames": processed_frames,
        **status_counts,
        "global_cell_count": int(global_cell_count),
        "global_finite_cell_count": int(global_finite_cell_count),
        "global_boundary_proxy_count": int(
            sum(int(row["boundary_proxy"]["selected_band_count"]) for row in rows)
        ),
        "global_boundary_proxy_fraction": _fraction(
            sum(int(row["boundary_proxy"]["selected_band_count"]) for row in rows),
            global_finite_cell_count,
        ),
        "boundary_proxy": {
            "selection_policy": "narrowest_nonempty",
            "selected_band_mode": selected_band_mode,
            "band_rows": band_rows,
        },
        "threshold_rows": threshold_rows,
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: RawBundle,
    lambda2_band_values: list[float],
    strain_thresholds: list[float],
    shell_step_limit: int,
    zero_eps: float,
    warnings: list[str],
) -> dict[str, Any]:
    frame_warning_start = len(warnings)
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": f"{bundle.path}#frame={snapshot}",
        "domain_length": float(bundle.domain_length),
        "grid_spacing": float(bundle.grid_spacing),
        "shell_step_limit": int(shell_step_limit),
    }

    try:
        u, v, w = _raw_velocity_frame(bundle, snapshot)
        strain, strain_frobenius, lambda2 = _strain_and_lambda2_from_velocity(u, v, w, bundle.domain_length)
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"reconstruction_failure: {exc}"]
        return row

    if not (np.isfinite(strain_frobenius).all() and np.isfinite(lambda2).all()):
        row["status"] = ERROR_STATUS
        row["errors"] = ["non-finite reconstruction values"]
        return row

    finite_mask = np.isfinite(lambda2) & np.isfinite(strain_frobenius)
    cell_count = int(lambda2.size)
    finite_cell_count = int(np.count_nonzero(finite_mask))
    if finite_cell_count != cell_count:
        warnings.append(f"frame {slot}: excluded {cell_count - finite_cell_count} non-finite reconstruction cells")

    row["cell_count"] = cell_count
    row["finite_cell_count"] = finite_cell_count
    row["lambda2_min"] = float(np.min(lambda2))
    row["lambda2_max"] = float(np.max(lambda2))
    row["strain_frobenius_min"] = float(np.min(strain_frobenius))
    row["strain_frobenius_max"] = float(np.max(strain_frobenius))

    band_rows: list[dict[str, Any]] = []
    selected_band = None
    selected_band_index = None
    selected_band_count = 0
    for index, band in enumerate(lambda2_band_values):
        boundary_mask = finite_mask & (np.abs(lambda2) <= float(band) + float(zero_eps))
        count = int(np.count_nonzero(boundary_mask))
        band_rows.append(
            {
                "band": float(band),
                "count": count,
                "fraction": _fraction(count, finite_cell_count),
                "selected": False,
            }
        )
        if selected_band is None and count > 0:
            selected_band = float(band)
            selected_band_index = int(index)
            selected_band_count = int(count)

    if selected_band is None:
        row["status"] = MISSING_REQUIRED_STATUS
        row["boundary_proxy"] = {
            "selection_policy": "narrowest_nonempty",
            "selected_band": None,
            "selected_band_index": None,
            "selected_band_count": 0,
            "selected_band_fraction": 0.0,
            "band_rows": band_rows,
        }
        row["threshold_rows"] = []
        row["errors"] = ["no non-empty lambda2 boundary proxy band was found"]
        return row

    band_rows[selected_band_index]["selected"] = True
    boundary_mask = finite_mask & (np.abs(lambda2) <= float(selected_band) + float(zero_eps))
    assignments = _periodic_shell_assignments(boundary_mask, shell_step_limit)
    row["boundary_proxy"] = {
        "selection_policy": "narrowest_nonempty",
        "selected_band": float(selected_band),
        "selected_band_index": int(selected_band_index),
        "selected_band_count": int(selected_band_count),
        "selected_band_fraction": _fraction(int(selected_band_count), finite_cell_count),
        "band_rows": band_rows,
    }

    threshold_rows: list[dict[str, Any]] = []
    for threshold in strain_thresholds:
        high_mask = finite_mask & (lambda2 >= -float(zero_eps)) & (strain_frobenius > float(threshold))
        high_count = int(np.count_nonzero(high_mask))
        counts, fractions = _threshold_bucket_counts(assignments, high_mask, shell_step_limit)
        (
            distance_step_min,
            distance_step_mean,
            distance_step_median,
            distance_step_max,
            distance_physical_min,
            distance_physical_mean,
            distance_physical_median,
            distance_physical_max,
        ) = _shell_distance_stats(counts, bundle.grid_spacing)
        threshold_rows.append(
            {
                "k0": float(threshold),
                "high_strain_count": int(high_count),
                "high_strain_fraction": _fraction(high_count, finite_cell_count),
                "high_strain_boundary_overlap_count": int(counts[0]),
                "high_strain_boundary_overlap_fraction": _fraction(int(counts[0]), high_count),
                "shell_step_limit": int(shell_step_limit),
                "shell_step_counts": [int(value) for value in counts],
                "shell_step_fractions": [float(value) for value in fractions],
                "shell_fraction_within_limit": _fraction(sum(counts[:-1]), high_count),
                "distance_step_min": distance_step_min,
                "distance_step_mean": distance_step_mean,
                "distance_step_median": distance_step_median,
                "distance_step_max": distance_step_max,
                "distance_physical_min": distance_physical_min,
                "distance_physical_mean": distance_physical_mean,
                "distance_physical_median": distance_physical_median,
                "distance_physical_max": distance_physical_max,
            }
        )

    row["threshold_rows"] = threshold_rows
    local_warnings = warnings[frame_warning_start:]
    row["status"] = OK_STATUS if not local_warnings or all(_is_benign_warning(warning) for warning in local_warnings) else PARTIAL_STATUS
    return row


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []

    lambda2_band_values = _sorted_unique_floats(list(args.lambda2_band_values), positive_only=True, allow_zero=False)
    strain_thresholds = _sorted_unique_floats(list(args.strain_thresholds), positive_only=False, allow_zero=True)

    if not args.raw_archive.exists():
        payload = _build_error_payload(args, [f"raw_archive_missing: {args.raw_archive}"], warnings)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty) + "\n"
        args.output.write_text(text, encoding="utf-8")
        print(text, end="")
        return 1

    if not lambda2_band_values:
        payload = _build_error_payload(args, ["lambda2_band_values parse to empty set"], warnings)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty) + "\n"
        args.output.write_text(text, encoding="utf-8")
        print(text, end="")
        return 1

    if not strain_thresholds:
        payload = _build_error_payload(args, ["strain_thresholds parse to empty set"], warnings)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty) + "\n"
        args.output.write_text(text, encoding="utf-8")
        print(text, end="")
        return 1

    try:
        bundle = _load_raw_bundle(args.raw_archive, warnings)
    except Exception as exc:
        payload = _build_error_payload(args, [f"raw_load_failure: {exc}"], warnings)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty) + "\n"
        args.output.write_text(text, encoding="utf-8")
        print(text, end="")
        return 1

    frame_indices = list(range(int(bundle.frame_count)))
    if args.frame is not None:
        if args.frame < 0 or args.frame >= int(bundle.frame_count):
            payload = _build_error_payload(
                args,
                [f"requested frame {args.frame} out of range for {bundle.frame_count} frames"],
                warnings,
            )
            args.output.parent.mkdir(parents=True, exist_ok=True)
            text = _json_text(payload, args.pretty) + "\n"
            args.output.write_text(text, encoding="utf-8")
            print(text, end="")
            return 1
        frame_indices = [int(args.frame)]
    frame_indices = frame_indices[: int(args.frame_limit)]
    selected_frames = [int(frame) for frame in frame_indices]

    rows: list[dict[str, Any]] = []
    for slot in frame_indices:
        row = _evaluate_frame(
            slot=int(slot),
            snapshot=int(slot),
            bundle=bundle,
            lambda2_band_values=lambda2_band_values,
            strain_thresholds=strain_thresholds,
            shell_step_limit=int(args.shell_step_limit),
            zero_eps=float(args.zero_eps),
            warnings=warnings,
        )
        rows.append(row)

    aggregate = _build_aggregate(rows, lambda2_band_values, strain_thresholds, int(args.shell_step_limit))

    if any(row.get("status") == ERROR_STATUS for row in rows):
        status = ERROR_STATUS
    elif any(row.get("status") == MISSING_REQUIRED_STATUS for row in rows):
        status = MISSING_REQUIRED_STATUS
    elif any(row.get("status") == PARTIAL_STATUS for row in rows):
        status = PARTIAL_STATUS
    elif any(not _is_benign_warning(warning) for warning in warnings):
        status = PARTIAL_STATUS
    else:
        status = OK_STATUS

    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        **CONTROL_CARD,
        "script": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "lambda2_band_values": lambda2_band_values,
            "strain_thresholds": strain_thresholds,
            "shell_step_limit": int(args.shell_step_limit),
            "selected_frames": selected_frames,
            "raw_bundle_frame_count": int(bundle.frame_count),
            "domain_length": float(bundle.domain_length),
            "grid_spacing": float(bundle.grid_spacing),
            "boundary_proxy_selection_policy": "narrowest_nonempty",
            "shell_metric": "periodic_26_neighborhood_steps",
        },
        "frames": rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": [],
        "changed_files": [str(args.output)],
    }
    if status in {ERROR_STATUS, MISSING_REQUIRED_STATUS}:
        payload["errors"] = ["scan completed with non-ok status"]

    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = _json_text(payload, args.pretty) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
