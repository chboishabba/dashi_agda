#!/usr/bin/env python3
"""Concentration diagnostic for top-vorticity overlap with Kato/biaxial carriers.

This diagnostic consumes a derived NS tensor archive and evaluates whether the
highest-vorticity cells align with the Kato/biaxial geometry:

* carrier : |lambda2| <= lambda2_band
* beta region : lambda2 <= beta

For selected top |omega| cells (by top-fraction or explicit top-k), it reports:
- overlap counts/fractions with carrier and beta masks
- median/min abs(lambda2) on the selected top cells
- nearest periodic carrier distances for top cells (SciPy distance-transform when
  available; capped brute-force fallback otherwise)
- worst-cell (max |omega|) metadata

This is fail-closed: missing required fields / invalid arguments / invalid
selection produce a non-ok status and explicit errors.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_boundary_geometric_concentration_diagnostic.py"
CONTRACT = "ns_boundary_geometric_concentration_diagnostic"
DEFAULT_OUTPUT = Path("outputs/ns_boundary_geometric_concentration_diagnostic.json")
DEFAULT_LAMBDA2_BAND = 1.0e-6
DEFAULT_TOP_FRACTION = 0.001
ROUTE_DECISION = "FAIL_CLOSED_GEOMETRIC_CONCENTRATION_DIAGNOSTIC"
OK_STATUS = "ok"
STATUS_MISSING = "missing_required_field"
STATUS_INVALID = "invalid_argument"
STATUS_NO_CARRIER = "no_carrier_cells"
TOP_DISTANCE_BRUTE_FORCE_CAP = 10000
OMEGA_COMPONENT_SETS = (
    ("omega_x", "omega_y", "omega_z"),
    ("omega1", "omega2", "omega3"),
    ("w_x", "w_y", "w_z"),
    ("wx", "wy", "wz"),
    ("vorticity_x", "vorticity_y", "vorticity_z"),
    ("vorticity1", "vorticity2", "vorticity3"),
)

try:
    from scipy.ndimage import distance_transform_edt as scipy_distance_transform_edt
except Exception:  # pragma: no cover - optional dependency path.
    scipy_distance_transform_edt = None


@dataclass(frozen=True)
class FieldBundle:
    lambda2: np.ndarray
    omega_norm: np.ndarray
    omega_norm_source: str
    beta: float
    beta_source: str


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


def _finite_named_float(name: str, value: str) -> float:
    try:
        parsed = float(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{name} must be a finite number") from exc
    if not math.isfinite(parsed):
        raise argparse.ArgumentTypeError(f"{name} must be finite")
    return parsed


def _finite_float(value: str) -> float:
    return _finite_named_float("value", value)


def _nonnegative_float(value: str) -> float:
    parsed = _finite_float(value)
    if parsed < 0.0:
        raise argparse.ArgumentTypeError("value must be nonnegative")
    return parsed


def _lambda2_band(value: str) -> float:
    return _finite_named_float("lambda2-band", value)


def _top_fraction(value: str) -> float:
    parsed = _nonnegative_float(value)
    if parsed <= 0.0 or parsed > 1.0:
        raise argparse.ArgumentTypeError("top-fraction must satisfy 0 < top-fraction <= 1")
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


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False)
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
            for key in ("grid_spacing", "domain_length", "length"):
                if key in meta and key not in payload:
                    payload[key] = np.asarray(meta[key])
    return payload


def _frame_scalar(value: np.ndarray, frame: int | None) -> float:
    arr = np.asarray(value)
    if arr.shape == ():
        scalar = arr.item()
    elif arr.ndim == 1 and arr.size == 1:
        scalar = arr[0]
    elif arr.ndim == 1:
        if frame is None:
            raise ValueError("beta is per-frame but --frame was not provided")
        if frame >= 0 and frame < int(arr.size):
            scalar = arr[frame]
        else:
            raise ValueError(f"beta frame {frame} is out of range for {arr.size} frame values")
    else:
        raise ValueError("beta is not a scalar")
    if not math.isfinite(float(scalar)):
        raise ValueError("beta is not finite")
    return float(scalar)


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


def _load_omega_norm(
    data: dict[str, np.ndarray],
    lambda2_shape: tuple[int, int, int],
    frame: int | None,
) -> tuple[np.ndarray, str]:
    if "omega_norm" in data:
        return _load_frame_field("omega_norm", data["omega_norm"], frame), "omega_norm"

    if "omega_norm_sq" in data:
        omega_norm_sq = _load_frame_field("omega_norm_sq", data["omega_norm_sq"], frame)
        if omega_norm_sq.shape != lambda2_shape:
            raise ValueError(
                f"omega_norm_sq shape {omega_norm_sq.shape!r} does not match lambda2 {lambda2_shape!r}"
            )
        min_sq = float(np.min(omega_norm_sq))
        if min_sq < -1.0e-15:
            raise ValueError("omega_norm_sq has significantly negative values")
        if min_sq < 0.0:
            omega_norm_sq = np.maximum(omega_norm_sq, 0.0)
        return np.sqrt(omega_norm_sq), "omega_norm_sq"

    for key_set in OMEGA_COMPONENT_SETS:
        if all(key in data for key in key_set):
            comps = [_load_frame_field(f"omega component {key}", data[key], frame) for key in key_set]
            for key, arr in zip(key_set, comps):
                if arr.shape != lambda2_shape:
                    raise ValueError(
                        f"omega component {key} shape {arr.shape!r} does not match lambda2 {lambda2_shape!r}"
                    )
            return np.sqrt(comps[0] ** 2 + comps[1] ** 2 + comps[2] ** 2), "+".join(key_set)

    raise KeyError("missing omega field")


def _load_bundle(path: Path, frame: int | None, beta_override: float | None) -> tuple[FieldBundle | None, list[str], list[str]]:
    warnings: list[str] = []
    try:
        data = _load_npz(path)
    except Exception as exc:
        return None, [f"input_archive:{exc}"], warnings

    if "lambda2" not in data:
        return None, ["missing lambda2"], warnings

    try:
        lambda2 = _load_frame_field("lambda2", data["lambda2"], frame)
    except Exception as exc:
        return None, [f"lambda2:{exc}"], warnings

    try:
        if beta_override is not None:
            beta = float(beta_override)
            if not math.isfinite(beta):
                raise ValueError("beta override must be finite")
            beta_source = "cli"
        elif "beta" in data:
            beta = _frame_scalar(data["beta"], frame)
            beta_source = "archive"
        else:
            return None, ["missing beta (pass --beta or include beta in archive)"], warnings
    except Exception as exc:
        return None, [f"beta:{exc}"], warnings

    try:
        omega_norm, omega_source = _load_omega_norm(data, lambda2.shape, frame)
    except KeyError as exc:
        return None, [f"missing vorticity field: {exc}"], warnings
    except Exception as exc:
        return None, [f"omega:{exc}"], warnings

    if lambda2.shape != omega_norm.shape:
        return (
            None,
            [f"shape_mismatch lambda2={lambda2.shape!r}, omega_norm={omega_norm.shape!r}"],
            warnings,
        )

    return (
        FieldBundle(
            lambda2=lambda2,
            omega_norm=omega_norm,
            omega_norm_source=omega_source,
            beta=float(beta),
            beta_source=beta_source,
        ),
        [],
        warnings,
    )


def _collect_top_indices(omega_norm: np.ndarray, top_k: int | None, top_fraction: float) -> np.ndarray:
    total = int(omega_norm.size)
    if total <= 0:
        return np.array([], dtype=np.int64)

    if top_k is None:
        raw = int(math.ceil(total * float(top_fraction)))
        k = max(1, raw)
    else:
        k = int(top_k)

    if k >= total:
        return np.arange(total, dtype=np.int64)

    flat = np.abs(omega_norm).ravel()
    top_local = np.argpartition(flat, -k)[-k:]
    top_vals = flat[top_local]
    order = np.argsort(top_vals)[::-1]
    return top_local[order]

def _nearest_carrier_distances_periodic(
    carrier_mask: np.ndarray,
    query_indices: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    shape = tuple(int(v) for v in carrier_mask.shape)
    nx, ny, nz = shape
    if not np.any(carrier_mask):
        inf = np.full((query_indices.shape[0],), float("inf"), dtype=np.float64)
        return inf, np.full((query_indices.shape[0], 3), -1, dtype=np.int64)

    if scipy_distance_transform_edt is None:
        raise RuntimeError("scipy_distance_transform_edt_unavailable")

    work = np.zeros((3 * nx, 3 * ny, 3 * nz), dtype=bool)
    for ix in range(3):
        sx = ix * nx
        ex = sx + nx
        for iy in range(3):
            sy = iy * ny
            ey = sy + ny
            for iz in range(3):
                sz = iz * nz
                ez = sz + nz
                work[sx:ex, sy:ey, sz:ez] = carrier_mask

    distances, indices = scipy_distance_transform_edt(
        ~work,
        return_indices=True,
    )
    q = np.asarray(query_indices, dtype=np.int64)
    qc = q + np.array([nx, ny, nz], dtype=np.int64)
    raw_x = indices[0, qc[:, 0], qc[:, 1], qc[:, 2]]
    raw_y = indices[1, qc[:, 0], qc[:, 1], qc[:, 2]]
    raw_z = indices[2, qc[:, 0], qc[:, 1], qc[:, 2]]
    nearest = np.column_stack((raw_x, raw_y, raw_z)).astype(np.int64)
    nearest_wrapped = np.empty_like(nearest)
    nearest_wrapped[:, 0] = nearest[:, 0] % nx
    nearest_wrapped[:, 1] = nearest[:, 1] % ny
    nearest_wrapped[:, 2] = nearest[:, 2] % nz
    return distances[qc[:, 0], qc[:, 1], qc[:, 2]], nearest_wrapped


def _brute_force_periodic_distances(
    carrier_indices: np.ndarray,
    query_indices: np.ndarray,
    shape: tuple[int, int, int],
) -> tuple[np.ndarray, np.ndarray]:
    if carrier_indices.size == 0:
        inf = np.full((query_indices.shape[0],), float("inf"), dtype=np.float64)
        return inf, np.full((query_indices.shape[0], 3), -1, dtype=np.int64)

    nx, ny, nz = shape
    periods = np.array([nx, ny, nz], dtype=np.float64)
    distances = np.empty(query_indices.shape[0], dtype=np.float64)
    nearest = np.empty((query_indices.shape[0], 3), dtype=np.int64)

    for i, q in enumerate(query_indices):
        delta = np.abs(carrier_indices - q)
        delta = np.minimum(delta, periods - delta)
        dist_sq = np.sum(delta.astype(np.float64) ** 2, axis=1)
        j = int(np.argmin(dist_sq))
        distances[i] = float(math.sqrt(float(dist_sq[j])))
        nearest[i] = carrier_indices[j]

    return distances, nearest


def _safe_stats(values: np.ndarray) -> dict[str, float | None]:
    if values.size == 0:
        return {"min": None, "mean": None, "median": None, "max": None}
    return {
        "min": float(np.min(values)),
        "mean": float(np.mean(values)),
        "median": float(np.median(values)),
        "max": float(np.max(values)),
    }


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    warnings: list[str] = []
    base_payload: dict[str, Any] = {
        "status": OK_STATUS,
        "schema_version": 1,
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        "inputs": {
            "derived_archive": str(args.derived_archive),
            "frame": args.frame,
            "lambda2_band": float(args.lambda2_band),
            "beta": None if args.beta is None else float(args.beta),
            "top_fraction": float(args.top_fraction),
            "top_k": None if args.top_k is None else int(args.top_k),
            "pretty": bool(args.pretty),
        },
        "O": "Emit fail-closed geometric concentration diagnostics for top-vorticity alignment.",
        "R": "Quantify overlap of top-|omega| cells with { |lambda2|<=lambda2_band } and {lambda2<=beta}.",
        "C": SCRIPT_NAME,
        "S": "Load a derived archive, resolve vorticity magnitude, select top cells, and measure nearest periodic-carrier distance.",
        "L": "Status is ok only when required fields/arguments are valid and top-cell selection is feasible.",
        "P": ROUTE_DECISION,
        "G": "This diagnostic is empirical only and does not assert theorem or Clay promotion.",
        "F": "The diagnostic is fail-closed: any missing required field, invalid argument, or invalid selection produces non-ok status.",
        "errors": [],
    }

    if not math.isfinite(args.lambda2_band) or args.lambda2_band < 0.0:
        base_payload.update({
            "status": STATUS_INVALID,
            "errors": ["invalid_lambda2_band"],
        })
        base_payload["warnings"] = sorted(set(warnings))
        return base_payload, 1

    if args.top_k is not None:
        if args.top_k <= 0:
            base_payload.update({
                "status": STATUS_INVALID,
                "errors": ["invalid_top_k"],
            })
            base_payload["warnings"] = sorted(set(warnings))
            return base_payload, 1

    if not math.isfinite(args.top_fraction) or args.top_fraction <= 0.0 or args.top_fraction > 1.0:
        base_payload.update({
            "status": STATUS_INVALID,
            "errors": ["invalid_top_fraction"],
        })
        base_payload["warnings"] = sorted(set(warnings))
        return base_payload, 1

    bundle, load_errors, load_warnings = _load_bundle(args.derived_archive, args.frame, args.beta)
    warnings.extend(load_warnings)
    base_payload["warnings"] = sorted(set(warnings))
    if bundle is None:
        base_payload["status"] = STATUS_MISSING
        base_payload["errors"] = sorted(set(load_errors))
        base_payload["warnings"] = sorted(set(warnings))
        return base_payload, 1

    warnings.append(f"omega_norm_source={bundle.omega_norm_source}")
    lambda2 = np.asarray(bundle.lambda2, dtype=np.float64)
    omega_norm = np.asarray(bundle.omega_norm, dtype=np.float64)
    beta = float(bundle.beta)

    if not np.all(np.isfinite(lambda2)) or not np.all(np.isfinite(omega_norm)):
        base_payload["status"] = STATUS_MISSING
        base_payload["errors"] = ["nonfinite_required_field"]
        base_payload["warnings"] = sorted(set(warnings))
        base_payload["beta_source"] = bundle.beta_source
        return base_payload, 1

    carrier_mask = np.abs(lambda2) <= float(args.lambda2_band)
    beta_mask = lambda2 <= beta
    total_cells = int(np.prod(lambda2.shape))
    if total_cells <= 0:
        base_payload["status"] = STATUS_MISSING
        base_payload["errors"] = ["empty_domain"]
        base_payload["warnings"] = sorted(set(warnings))
        return base_payload, 1

    top_indices = _collect_top_indices(omega_norm, args.top_k, args.top_fraction)
    if top_indices.size == 0:
        base_payload["status"] = STATUS_INVALID
        base_payload["errors"] = ["top_selection_empty"]
        base_payload["warnings"] = sorted(set(warnings))
        return base_payload, 1

    top_k = int(top_indices.size)
    if args.top_k is not None and top_k < args.top_k:
        warnings.append(f"top_k_capped_to_total_cells_{top_k}")
    if args.top_k is not None and args.top_k > top_k:
        top_request = int(args.top_k)
    elif args.top_k is None:
        top_request = int(math.ceil(total_cells * float(args.top_fraction)))
    else:
        top_request = top_k

    top_indices_multi = np.unravel_index(top_indices, lambda2.shape)
    top_cells = np.column_stack((top_indices_multi[0], top_indices_multi[1], top_indices_multi[2])).astype(np.int64)

    carrier_top_count = int(np.count_nonzero(carrier_mask.ravel()[top_indices]))
    beta_top_count = int(np.count_nonzero(beta_mask.ravel()[top_indices]))
    carrier_count = int(np.count_nonzero(carrier_mask))
    beta_count = int(np.count_nonzero(beta_mask))
    top_lambda2 = np.abs(lambda2.ravel()[top_indices])
    top_omega = omega_norm.ravel()[top_indices]

    worst_flat = int(top_indices[0])  # max selected |omega| (top selection is descending)
    worst_idx = np.unravel_index(worst_flat, lambda2.shape)
    worst = {
        "flat_index": int(worst_flat),
        "index": [int(v) for v in worst_idx],
        "omega": float(omega_norm[worst_idx]),
        "omega_abs": float(abs(omega_norm[worst_idx])),
        "lambda2": float(lambda2[worst_idx]),
        "lambda2_abs": float(abs(lambda2[worst_idx])),
        "on_carrier": bool(carrier_mask[worst_idx]),
        "on_beta": bool(beta_mask[worst_idx]),
    }

    distances_cells: np.ndarray
    nearest_cells: np.ndarray
    distance_method = "uncomputed"
    distance_computed = 0
    if not np.any(carrier_mask):
        warnings.append("carrier_mask_empty; nearest-carrier distance unavailable")
        distances_cells = np.full((top_k,), float("inf"), dtype=np.float64)
        nearest_cells = np.full((top_k, 3), -1, dtype=np.int64)
    else:
        if scipy_distance_transform_edt is not None:
            try:
                distances_cells, nearest_cells = _nearest_carrier_distances_periodic(carrier_mask, top_cells)
                distance_method = "scipy_distance_transform_periodic"
                distance_computed = int(top_cells.shape[0])
            except Exception as exc:  # pragma: no cover - defensive.
                warnings.append(f"scipy_distance_transform_failed:{exc}")

        if scipy_distance_transform_edt is None or distance_computed == 0:
            if top_k > TOP_DISTANCE_BRUTE_FORCE_CAP:
                warnings.append(
                    f"top-distance_bruteforce_capped_at_{TOP_DISTANCE_BRUTE_FORCE_CAP}_without_scipy"
                )
                compute_cells = top_cells[:TOP_DISTANCE_BRUTE_FORCE_CAP]
            else:
                compute_cells = top_cells

            distance_method = "brute_force_periodic"
            flat_carrier = np.argwhere(carrier_mask)
            if flat_carrier.size == 0:
                distances_cells_full = np.full((top_k,), float("inf"), dtype=np.float64)
                nearest_cells = np.full((top_k, 3), -1, dtype=np.int64)
            else:
                dsel, nearest_sel = _brute_force_periodic_distances(
                    flat_carrier.astype(np.int64),
                    compute_cells,
                    lambda2.shape,
                )
                distances_cells_full = np.full((top_k,), float("inf"), dtype=np.float64)
                nearest_cells = np.full((top_k, 3), -1, dtype=np.int64)
                distances_cells_full[: dsel.size] = dsel
                nearest_cells[: nearest_sel.shape[0]] = nearest_sel
            distances_cells = distances_cells_full
            distance_computed = int(np.count_nonzero(np.isfinite(distances_cells)))

            if top_k > TOP_DISTANCE_BRUTE_FORCE_CAP:
                warnings.append("scipy_unavailable_or_failed; nearest distances computed for capped prefix only")

    finite_distances = np.asarray(distances_cells[np.isfinite(distances_cells)], dtype=np.float64)
    nearest_distance_stats = _safe_stats(finite_distances)

    nearest_distance_stats.update(
        {
            "computed_count": distance_computed,
            "requested_count": int(top_k),
            "method": distance_method,
            "source": "top_cells",
        }
    )

    if worst["index"] is not None:
        worst_flat_pos = int(np.where(top_indices == worst_flat)[0][0])
        if np.isfinite(distances_cells[worst_flat_pos]):
            worst["nearest_carrier_index"] = [int(v) for v in nearest_cells[worst_flat_pos]]
            worst["nearest_carrier_distance_cells"] = float(distances_cells[worst_flat_pos])

    payload = base_payload
    payload["shape"] = [int(v) for v in lambda2.shape]
    payload["lambda2_band"] = float(args.lambda2_band)
    payload["beta"] = float(beta)
    payload["beta_source"] = bundle.beta_source
    payload["top_k_requested"] = None if args.top_k is None else int(args.top_k)
    payload["top_k_selected"] = int(top_k)
    payload["top_cell_count"] = int(top_k)
    payload["selected_top_cell_count"] = int(top_k)
    payload["top_k_effective_request"] = int(top_request)
    payload["top_fraction"] = float(args.top_fraction)
    payload["total_cells"] = total_cells
    payload["analysis_cell_count"] = total_cells
    payload["carrier_mask_cells"] = carrier_count
    payload["beta_mask_cells"] = beta_count
    payload["carrier_fraction"] = None if total_cells <= 0 else float(carrier_count / float(total_cells))
    payload["beta_fraction"] = None if total_cells <= 0 else float(beta_count / float(total_cells))
    payload["top_on_carrier_count"] = int(carrier_top_count)
    payload["top_on_beta_count"] = int(beta_top_count)
    payload["top_on_carrier_fraction"] = float(carrier_top_count / float(top_k))
    payload["top_on_beta_fraction"] = float(beta_top_count / float(top_k))
    payload["top_lambda2_abs_min"] = float(np.min(top_lambda2))
    payload["top_lambda2_abs_median"] = float(np.median(top_lambda2))
    payload["top_omega_abs_max"] = float(np.max(top_omega))
    payload["top_omega_abs_median"] = float(np.median(top_omega))
    payload["top_omega_abs_min"] = float(np.min(top_omega))
    payload["top_cells_worst"] = worst
    payload["worst_cell"] = worst
    payload["worst_cell_index"] = worst["index"]
    payload["worst_cell_value"] = worst["omega_abs"]
    payload["nearest_carrier_distance_cells"] = nearest_distance_stats
    payload["errors"] = []
    payload["warnings"] = sorted(set(warnings))
    payload["status"] = OK_STATUS if payload["errors"] == [] else payload["status"]

    if carrier_count == 0:
        payload["status"] = STATUS_NO_CARRIER
        payload["errors"] = ["carrier_mask_empty"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload, 1

    return payload, 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--derived-archive", type=Path, required=True, help="derived tensor archive in NPZ form")
    parser.add_argument("--frame", type=_nonnegative_int, default=None, help="frame index for 4D archives")
    parser.add_argument(
        "--lambda2-band",
        type=_lambda2_band,
        default=DEFAULT_LAMBDA2_BAND,
        help="abs(lambda2)-band for Kato/biaxial carrier.",
    )
    parser.add_argument("--beta", type=_finite_float, default=None, help="override beta threshold")
    parser.add_argument(
        "--top-fraction",
        type=_top_fraction,
        default=DEFAULT_TOP_FRACTION,
        help="fraction of highest-|omega| cells used as top set",
    )
    parser.add_argument("--top-k", type=_positive_int, default=None, help="explicit number of top-|omega| cells")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="write payload to JSON file")
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON output.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload, code = _build_payload(args)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        _json_text(payload, pretty=args.pretty) + ("\n" if args.pretty else ""),
        encoding="utf-8",
    )
    return code


if __name__ == "__main__":
    raise SystemExit(main())
