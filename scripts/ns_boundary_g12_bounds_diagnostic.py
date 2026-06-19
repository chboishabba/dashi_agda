#!/usr/bin/env python3
"""Boundary g12 bound diagnostic for derived NS tensor archives.

Consumes a derived tensor ``.npz`` archive and reports:

- global ``g12`` statistics over the selected frame/domain,
- boundary-carrier statistics on ``|lambda2| <= lambda2_band``,
- beta-region statistics on ``lambda2 <= beta``,
- flags ``finite_positive_min`` and ``finite_upper_bound_observed``.

This diagnostic is deterministic and fail-closed: any validation or loading
failure sets a non-``ok`` status and is explicitly recorded in ``errors``.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_boundary_g12_bounds_diagnostic.py"
CONTRACT = "ns_boundary_g12_bounds_diagnostic"
PRODUCER_NAME = "scripts/ns_boundary_derived_tensor_archive.py"
DEFAULT_OUTPUT = Path("outputs/ns_boundary_g12_bounds_diagnostic.json")
DEFAULT_LAMBDA2_BAND = 1.0e-3
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_G12_BOUNDS_DIAGNOSTIC"

OK_STATUS = "ok"
STATUS_MISSING = "missing_required_field"
STATUS_INVALID = "invalid_argument"
STATUS_NO_BOUNDARY = "no_boundary_cells"
STATUS_NO_BETA = "no_beta_cells"


@dataclass(frozen=True)
class FieldBundle:
    lambda2: np.ndarray
    g12: np.ndarray
    beta: float
    beta_source: str
    shape: tuple[int, int, int]


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


def _finite_nonnegative_float(name: str, value: float) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError(f"{name} must be finite and nonnegative")
    return parsed


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("frame must be nonnegative")
    return parsed


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {name: np.asarray(data[name]) for name in data.files}


def _coerce_scalar_like(
    value: Any,
    field: str,
    frame: int | None,
) -> float:
    arr = np.asarray(value)
    if arr.ndim == 0:
        raw = arr.item()
    elif arr.ndim == 1 and arr.size == 1:
        raw = arr.reshape(()).item()
    elif arr.ndim == 1 and frame is not None:
        if frame < 0 or frame >= int(arr.size):
            raise ValueError(f"{field} frame {frame} is out of range")
        raw = arr[frame]
    else:
        raise ValueError(f"{field} must be scalar (or 1D with --frame)")

    if isinstance(raw, bytes):
        raw = raw.decode("utf-8")
    if isinstance(raw, np.generic):
        raw = raw.item()
    if isinstance(raw, bool):
        raise ValueError(f"{field} must be numeric, not bool")
    scalar = float(raw)
    if not math.isfinite(scalar):
        raise ValueError(f"{field} must be finite")
    return float(scalar)


def _load_frame_field(name: str, raw: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(raw, dtype=np.float64)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) != 1:
                raise ValueError(
                    f"{name} has {int(arr.shape[0])} frame(s); pass --frame to select one"
                )
            arr = arr[0]
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {int(arr.shape[0])} frame(s)")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be 3D (or single-snapshot 4D), got {arr.shape!r}")
    if arr.shape[0] <= 0 or arr.shape[1] <= 0 or arr.shape[2] <= 0:
        raise ValueError(f"{name} has invalid shape {arr.shape!r}")
    return np.asarray(arr, dtype=np.float64)


def _load_bundle(
    path: Path,
    frame: int | None,
    beta_override: float | None,
) -> tuple[FieldBundle | None, list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    try:
        data = _load_npz(path)
    except FileNotFoundError:
        return None, ["missing_input_archive"], []
    except Exception as exc:
        return None, [f"input_archive:{exc}"], []

    if "lambda2" not in data:
        return None, ["missing_lambda2"], []
    if "g12" not in data:
        return None, ["missing_g12"], []

    try:
        lambda2 = _load_frame_field("lambda2", data["lambda2"], frame)
        g12 = _load_frame_field("g12", data["g12"], frame)
    except Exception as exc:
        return None, [f"field_load:{exc}"], []

    if lambda2.shape != g12.shape:
        return None, [f"shape_mismatch:lambda2={lambda2.shape!r},g12={g12.shape!r}"], []
    if lambda2.ndim != 3:
        return None, [f"unsupported_field_rank:lambda2={lambda2.ndim}"], []

    lambda2_finite = np.isfinite(lambda2)
    g12_finite = np.isfinite(g12)
    if not np.all(lambda2_finite):
        warnings.append("nonfinite_lambda2_cells")
    if not np.all(g12_finite):
        warnings.append("nonfinite_g12_cells")

    if beta_override is not None:
        try:
            beta = _finite_nonnegative_float("--beta", beta_override)
        except Exception as exc:
            return None, [f"invalid_beta:{exc}"], []
        beta_source = "cli"
    else:
        if "beta" not in data:
            return None, ["missing_beta"], []
        try:
            beta = _coerce_scalar_like(data["beta"], "beta", frame)
        except Exception as exc:
            return None, [f"beta:{exc}"], []
        if beta < 0.0:
            return None, ["beta_negative"], []
        beta_source = "archive"

    return (
        FieldBundle(
            lambda2=lambda2,
            g12=g12,
            beta=float(beta),
            beta_source=beta_source,
            shape=(int(lambda2.shape[0]), int(lambda2.shape[1]), int(lambda2.shape[2])),
        ),
        [],
        sorted(set(warnings)),
    )


def _safe_stats(values: np.ndarray, mask: np.ndarray | None = None) -> dict[str, Any]:
    if mask is None:
        mask = np.ones(values.shape, dtype=bool)
    mask = np.asarray(mask, dtype=bool)
    if mask.shape != values.shape:
        raise ValueError(f"mask shape {mask.shape!r} does not match values {values.shape!r}")

    cell_count = int(mask.size) if mask.ndim == values.ndim and np.all(mask) else int(np.count_nonzero(mask))
    finite_mask = np.isfinite(values) & mask
    finite_count = int(np.count_nonzero(finite_mask))
    nonfinite_count = int(cell_count - finite_count)

    if finite_count == 0:
        return {
            "cell_count": int(cell_count),
            "finite_cell_count": 0,
            "nonfinite_cell_count": int(nonfinite_count),
            "min": None,
            "max": None,
            "mean": None,
            "sum": None,
            "finite_positive_min": None,
        }

    finite_values = np.asarray(values, dtype=np.float64)[finite_mask]
    return {
        "cell_count": int(cell_count),
        "finite_cell_count": int(finite_count),
        "nonfinite_cell_count": int(nonfinite_count),
        "min": float(np.min(finite_values)),
        "max": float(np.max(finite_values)),
        "mean": float(np.mean(finite_values)),
        "sum": float(np.sum(finite_values)),
        "finite_positive_min": float(np.min(finite_values[finite_values > 0.0])) if np.any(finite_values > 0.0) else None,
    }


def _set_status(
    bundle: FieldBundle,
    global_stats: dict[str, Any],
    boundary_stats: dict[str, Any],
    beta_stats: dict[str, Any],
    warnings: list[str],
    errors: list[str],
) -> str:
    if errors:
        return STATUS_INVALID
    if global_stats.get("finite_cell_count", 0) == 0:
        return STATUS_INVALID
    if boundary_stats.get("cell_count", 0) == 0:
        return STATUS_NO_BOUNDARY
    if boundary_stats.get("finite_cell_count", 0) == 0:
        return STATUS_INVALID
    if beta_stats.get("finite_cell_count", 0) == 0:
        return STATUS_INVALID
    if beta_stats.get("cell_count", 0) == 0:
        return STATUS_NO_BETA
    if warnings:
        return OK_STATUS
    if not bundle.beta >= 0.0:
        return STATUS_INVALID
    return OK_STATUS


def _build_payload(args: argparse.Namespace) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "producer": PRODUCER_NAME,
        "route_decision": ROUTE_DECISION,
        "input": str(args.derived_archive),
        "frame": None if args.frame is None else int(args.frame),
        "lambda2_band": float(args.lambda2_band),
        "authority": _authority(),
        "warnings": [],
        "errors": [],
        "O": "Emit a deterministic fail-closed diagnostic of g12 statistics over global, boundary-carrier, and beta-mask regions.",
        "R": "Load a derived NS tensor archive and evaluate g12 finite statistics on frame/domain, |lambda2|<=lambda2_band, and lambda2<=beta sets.",
        "C": SCRIPT_NAME,
        "S": "Validate arguments, required fields, masking, and finite masks; then emit explicit status and structured statistics.",
        "L": "Status is ok only when required fields parse correctly and both masks are non-empty with finite support.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or promotion claim is asserted by this diagnostic.",
        "F": "Fail-closed empirical diagnostic; authority markers remain non-promoting.",
    }

    if not math.isfinite(args.lambda2_band) or args.lambda2_band < 0.0:
        payload["status"] = STATUS_INVALID
        payload["errors"] = ["invalid_lambda2_band"]
        payload["global_g12_stats"] = None
        payload["boundary_carrier_stats"] = None
        payload["beta_mask_stats"] = None
        payload["finite_positive_min"] = False
        payload["finite_upper_bound_observed"] = False
        payload["warnings"] = []
        return payload

    bundle, errors, warnings = _load_bundle(args.derived_archive, args.frame, args.beta)
    payload["warnings"].extend(warnings)
    if bundle is None:
        payload["status"] = STATUS_MISSING
        payload["errors"] = sorted(set(errors))
        payload["global_g12_stats"] = None
        payload["boundary_carrier_stats"] = None
        payload["beta_mask_stats"] = None
        payload["finite_positive_min"] = False
        payload["finite_upper_bound_observed"] = False
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload

    payload["warnings"] = sorted(set(payload["warnings"]))

    boundary_mask = np.asarray(np.abs(bundle.lambda2) <= float(args.lambda2_band), dtype=bool)
    beta_mask = np.asarray(bundle.lambda2 <= bundle.beta, dtype=bool)
    payload["beta"] = float(bundle.beta)
    payload["beta_source"] = bundle.beta_source
    payload["shape"] = [int(v) for v in bundle.shape]
    payload["boundary_mask_cell_count"] = int(np.count_nonzero(boundary_mask))
    payload["beta_mask_cell_count"] = int(np.count_nonzero(beta_mask))

    global_stats = _safe_stats(bundle.g12, None)
    boundary_stats = _safe_stats(bundle.g12, boundary_mask)
    beta_stats = _safe_stats(bundle.g12, beta_mask)
    payload["global_g12_stats"] = global_stats
    payload["boundary_carrier_stats"] = boundary_stats
    payload["beta_mask_stats"] = beta_stats

    finite_values = np.asarray(bundle.g12, dtype=np.float64)[np.isfinite(bundle.g12)]
    finite_positive = finite_values[finite_values > 0.0]
    finite_positive_min = bool(finite_positive.size > 0)
    finite_upper_bound_observed = bool(finite_values.size > 0 and np.isfinite(finite_values.max()))
    payload["finite_positive_min"] = finite_positive_min
    payload["finite_positive_min_value"] = None if not finite_positive_min else float(np.min(finite_positive))
    payload["finite_upper_bound_observed"] = finite_upper_bound_observed

    payload["errors"] = []
    if not np.all(np.isfinite(bundle.lambda2)):
        payload["errors"].append("nonfinite_lambda2")
    if not np.all(np.isfinite(bundle.g12)):
        payload["errors"].append("nonfinite_g12")
    payload["errors"] = sorted(set(payload["errors"]))
    payload["warnings"] = sorted(set(payload["warnings"]))

    payload["status"] = _set_status(bundle, global_stats, boundary_stats, beta_stats, payload["warnings"], payload["errors"])
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--derived-archive",
        type=Path,
        required=True,
        help="Derived NS tensor archive (.npz) containing lambda2/g12 and optional beta.",
    )
    parser.add_argument(
        "--frame",
        type=_nonnegative_int,
        default=None,
        help="Optional frame index for frame-indexed fields (required when fields have leading frame axis > 1).",
    )
    parser.add_argument(
        "--lambda2-band",
        type=float,
        default=DEFAULT_LAMBDA2_BAND,
        help="Boundary-carrier band for abs(lambda2).",
    )
    parser.add_argument(
        "--beta",
        type=float,
        default=None,
        help="Override beta threshold; otherwise read from archive beta field.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output JSON report path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = _build_payload(args)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        _json_text(payload, args.pretty) + ("\n" if args.pretty else ""),
        encoding="utf-8",
    )
    return 0 if payload.get("status") == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
