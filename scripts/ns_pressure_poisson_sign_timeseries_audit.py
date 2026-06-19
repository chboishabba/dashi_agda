#!/usr/bin/env python3
"""Audit pressure-Poisson sign conventions across a frame series.

The script consumes a raw NS pressure archive with ``pressure_snapshots``,
``velocity_snapshots``, and optionally ``omega_snapshots``. For each selected
frame it computes a spectral ``Delta p`` and ``-Delta p`` from the pressure
snapshot, builds the source proxy ``tr(S^2) - |omega|^2 / 4`` from velocity
data, and records which sign fits best together with the positive best scale,
correlations, and RMSE values.

The output is deterministic JSON, fail-closed, and deliberately non-promoting:
it reports aggregate sign counts, scale statistics, and sign stability but does
not claim theorem or authority status.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

from ns_pressure_poisson_sign_audit import (
    CONTROL_CARD,
    OK_STATUS,
    PRESSURE_KEYS,
    STATUS_MISSING_REQUIRED_FIELD,
    STATUS_NO_PROXY,
    VELOCITY_COMPONENT_SETS,
    _best_sign_proxy,
    _load_npz,
    _load_pressure_field,
    _load_vector_components,
    _resolve_domain_length,
    _spectral_laplacian,
    _strain_tensor,
    _tensor_frobenius_squared,
    _velocity_gradient,
    _vector_norm_squared,
    _vorticity_from_gradient,
)

SCRIPT_NAME = "scripts/ns_pressure_poisson_sign_timeseries_audit.py"
CONTRACT = "ns_pressure_poisson_sign_timeseries_audit"
DEFAULT_OUTPUT = Path("outputs/ns_pressure_poisson_sign_timeseries_audit.json")
ERROR_STATUS = "error"


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
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


def _nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be a nonnegative integer")
    return parsed


def _parse_frame_spec(spec: str | None, frame_count: int) -> list[int]:
    if spec is None:
        return list(range(frame_count))

    text = spec.strip()
    if not text or text.lower() == "all":
        return list(range(frame_count))

    selected: set[int] = set()
    for chunk in text.split(","):
        token = chunk.strip()
        if not token:
            continue
        if "-" in token:
            start_text, end_text = token.split("-", 1)
            if not start_text or not end_text:
                raise ValueError(f"invalid frame range {token!r}")
            start = _nonnegative_int(start_text)
            end = _nonnegative_int(end_text)
            if end < start:
                raise ValueError(f"invalid frame range {token!r}: end must be >= start")
            selected.update(range(start, end + 1))
        else:
            selected.add(_nonnegative_int(token))

    frame_indices = sorted(selected)
    if not frame_indices:
        raise ValueError("frame selection is empty")
    if frame_indices[0] < 0 or frame_indices[-1] >= frame_count:
        raise ValueError(f"frame selection {frame_indices!r} is out of range for {frame_count} frame(s)")
    return frame_indices


def _frame_count_from_pressure(data: dict[str, np.ndarray]) -> tuple[int, np.ndarray, str]:
    for key in PRESSURE_KEYS:
        if key not in data:
            continue
        arr = np.asarray(data[key])
        if np.iscomplexobj(arr):
            if arr.ndim == 3:
                return 1, arr, key
            if arr.ndim == 4:
                return int(arr.shape[0]), arr, key
            raise ValueError(f"{key} must be 3D or 4D complex data, got {arr.shape!r}")
        if arr.ndim == 3:
            return 1, arr, key
        if arr.ndim == 4:
            return int(arr.shape[0]), arr, key
        raise ValueError(f"{key} must be 3D or 4D data, got {arr.shape!r}")
    raise ValueError("missing required pressure field")


def _frame_stats(field: np.ndarray) -> dict[str, float]:
    arr = np.asarray(field, dtype=np.float64)
    return {
        "min": float(np.min(arr)),
        "mean": float(np.mean(arr)),
        "max": float(np.max(arr)),
        "rmse_vs_zero": float(np.sqrt(np.mean(arr * arr))),
    }


def _source_proxy_for_frame(data: dict[str, np.ndarray], frame: int, pressure_shape: tuple[int, int, int], domain_length: float) -> tuple[np.ndarray | None, str | None, list[str]]:
    source_proxy = None
    source_proxy_source = None
    notes: list[str] = []

    components, vector_source = _load_vector_components(data, frame, VELOCITY_COMPONENT_SETS)
    if components is None or vector_source is None:
        return None, None, notes

    u, v, w = components
    if u.shape != pressure_shape or v.shape != pressure_shape or w.shape != pressure_shape:
        notes.append(
            f"velocity shapes do not match pressure: u={u.shape!r}, v={v.shape!r}, w={w.shape!r}, pressure={pressure_shape!r}"
        )
        return None, None, notes

    grad = _velocity_gradient(u, v, w, domain_length)
    strain = _strain_tensor(grad)
    omega = _vorticity_from_gradient(grad)
    source_proxy = _tensor_frobenius_squared(strain) - 0.25 * _vector_norm_squared(omega)
    source_proxy_source = f"computed_from_{vector_source}"
    notes.append("source proxy computed spectrally from velocity")
    return source_proxy, source_proxy_source, notes


def _comparison_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    valid_rows = [row for row in rows if row.get("status") == OK_STATUS and row.get("best_sign_proxy")]
    total = len(valid_rows)
    minus_rows = [row for row in valid_rows if row["best_sign_proxy"]["sign"] == "minus"]
    plus_rows = [row for row in valid_rows if row["best_sign_proxy"]["sign"] == "plus"]

    def _safe(values: list[float]) -> dict[str, float] | None:
        if not values:
            return None
        arr = np.asarray(values, dtype=np.float64)
        return {
            "min": float(np.min(arr)),
            "mean": float(np.mean(arr)),
            "median": float(np.median(arr)),
            "max": float(np.max(arr)),
            "std": float(np.std(arr)),
        }

    best_scales = [float(row["best_sign_proxy"]["best_scale"]) for row in valid_rows]
    raw_rmse = [float(row["best_sign_proxy"]["raw_rmse"]) for row in valid_rows]
    scaled_rmse = [float(row["best_sign_proxy"]["scaled_rmse"]) for row in valid_rows]
    raw_corr = [float(row["best_sign_proxy"]["raw_correlation"]) for row in valid_rows if row["best_sign_proxy"]["raw_correlation"] is not None]
    scaled_corr = [
        float(row["best_sign_proxy"]["scaled_correlation"])
        for row in valid_rows
        if row["best_sign_proxy"]["scaled_correlation"] is not None
    ]

    return {
        "valid_frame_count": total,
        "best_sign_counts": {"minus": len(minus_rows), "plus": len(plus_rows)},
        "best_sign_fraction": {
            "minus": (len(minus_rows) / total) if total else None,
            "plus": (len(plus_rows) / total) if total else None,
        },
        "best_scale_stats": _safe(best_scales),
        "raw_rmse_stats": _safe(raw_rmse),
        "scaled_rmse_stats": _safe(scaled_rmse),
        "raw_correlation_stats": _safe(raw_corr),
        "scaled_correlation_stats": _safe(scaled_corr),
    }


def _sign_stability(rows: list[dict[str, Any]]) -> dict[str, Any]:
    signs = [row["best_sign_proxy"]["sign"] for row in rows if row.get("status") == OK_STATUS and row.get("best_sign_proxy")]
    if not signs:
        return {
            "modal_sign": None,
            "modal_count": 0,
            "modal_fraction": None,
            "all_same": False,
            "sign_changes": 0,
            "longest_run": 0,
        }

    counts = {"minus": signs.count("minus"), "plus": signs.count("plus")}
    modal_sign = "minus" if counts["minus"] >= counts["plus"] else "plus"
    modal_count = counts[modal_sign]

    sign_changes = sum(1 for left, right in zip(signs, signs[1:]) if left != right)
    longest_run = 1
    current_run = 1
    for left, right in zip(signs, signs[1:]):
        if left == right:
            current_run += 1
        else:
            longest_run = max(longest_run, current_run)
            current_run = 1
    longest_run = max(longest_run, current_run)

    return {
        "modal_sign": modal_sign,
        "modal_count": modal_count,
        "modal_fraction": modal_count / len(signs),
        "all_same": modal_count == len(signs),
        "sign_changes": sign_changes,
        "longest_run": longest_run,
    }


def _build_frame_row(data: dict[str, np.ndarray], frame: int, domain_length: float) -> dict[str, Any]:
    row: dict[str, Any] = {"frame": frame, "status": OK_STATUS}

    try:
        pressure, pressure_source = _load_pressure_field(data, frame)
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"pressure_load:{exc}"]
        return row

    if pressure is None:
        row["status"] = STATUS_MISSING_REQUIRED_FIELD
        row["errors"] = ["missing_pressure_field"]
        return row

    if pressure.ndim != 3:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"pressure_shape:{pressure.shape!r}"]
        return row

    n = int(pressure.shape[0])
    if pressure.shape[1] != n or pressure.shape[2] != n:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"pressure_shape:{pressure.shape!r}"]
        return row

    try:
        frame_domain_length, domain_source = _resolve_domain_length(data, n, domain_length)
    except Exception as exc:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"domain_length:{exc}"]
        return row

    laplacian_pressure = _spectral_laplacian(pressure, frame_domain_length)
    negative_laplacian_pressure = -laplacian_pressure

    source_proxy, source_proxy_source, source_proxy_notes = _source_proxy_for_frame(
        data,
        frame,
        pressure.shape,
        frame_domain_length,
    )
    if source_proxy is None:
        row["status"] = STATUS_NO_PROXY
        row["errors"] = ["proxy_unavailable"]
        row["pressure_source"] = pressure_source
        row["pressure_shape"] = list(map(int, pressure.shape))
        row["domain_length"] = float(frame_domain_length)
        row["domain_length_source"] = domain_source
        row["source_proxy_available"] = False
        row["source_proxy_source"] = source_proxy_source
        row["source_proxy_notes"] = source_proxy_notes
        row["spectral_delta_p"] = _frame_stats(laplacian_pressure)
        row["spectral_negative_delta_p"] = _frame_stats(negative_laplacian_pressure)
        return row

    if source_proxy.shape != pressure.shape:
        row["status"] = ERROR_STATUS
        row["errors"] = [f"source_proxy_shape:{source_proxy.shape!r}", f"pressure_shape:{pressure.shape!r}"]
        return row

    if not np.all(np.isfinite(source_proxy)):
        row["status"] = ERROR_STATUS
        row["errors"] = ["nonfinite_source_proxy"]
        return row

    best_sign_proxy, comparisons, violation = _best_sign_proxy(source_proxy, laplacian_pressure)

    row.update(
        {
            "pressure_source": pressure_source,
            "pressure_shape": list(map(int, pressure.shape)),
            "domain_length": float(frame_domain_length),
            "domain_length_source": domain_source,
            "source_proxy_available": True,
            "source_proxy_source": source_proxy_source,
            "source_proxy_notes": source_proxy_notes,
            "source_proxy_stats": _frame_stats(source_proxy),
            "spectral_delta_p": _frame_stats(laplacian_pressure),
            "spectral_negative_delta_p": _frame_stats(negative_laplacian_pressure),
            "best_sign_proxy": best_sign_proxy,
            "comparisons": comparisons,
            "violation": violation,
            "best_sign": best_sign_proxy["sign"],
            "best_scale": float(best_sign_proxy["best_scale"]),
            "raw_correlation": best_sign_proxy["raw_correlation"],
            "scaled_correlation": best_sign_proxy["scaled_correlation"],
            "raw_rmse": float(best_sign_proxy["raw_rmse"]),
            "scaled_rmse": float(best_sign_proxy["scaled_rmse"]),
        }
    )
    return row


def _build_payload(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "input": str(args.input),
        "frames": args.frames,
        "output_json": str(args.output_json),
        "pretty": bool(args.pretty),
        "requested_domain_length": args.domain_length,
        "contract": CONTRACT,
        "authority": _authority(),
        "status": STATUS_MISSING_REQUIRED_FIELD,
        "errors": [],
        "warnings": [],
        "O": CONTROL_CARD["O"],
        "R": "Compare tr(S^2) - |omega|^2 / 4 against +Delta p and -Delta p for each selected frame.",
        "C": CONTROL_CARD["C"],
        "S": CONTROL_CARD["S"],
        "L": "pressure frame -> spectral Laplacian -> velocity-derived source proxy -> per-frame sign ranking -> aggregate stability",
        "P": "Use the majority sign, scale spread, and sign-change count to localize the convention drift across time.",
        "G": "Authority stays false and no theorem or Clay promotion is claimed.",
        "F": "Missing pressure or proxy data blocks a definitive timeseries sign audit.",
        "frame_count": None,
        "selected_frame_count": None,
        "frame_indices": [],
        "selected_frames": [],
        "pressure_source": None,
        "source_proxy_source": None,
        "domain_length": None,
        "domain_length_source": None,
        "rows": [],
        "aggregate_counts": {},
        "aggregate_metrics": {},
        "sign_stability": {},
        "changed_paths": [str(args.output_json)],
    }

    try:
        data = _load_npz(args.input)
    except FileNotFoundError:
        payload["errors"] = ["input_archive"]
        return payload, 1
    except Exception as exc:
        payload["errors"] = [f"input_archive:{exc}"]
        return payload, 1

    try:
        frame_count, pressure_raw, pressure_source = _frame_count_from_pressure(data)
    except Exception as exc:
        payload["errors"] = [f"pressure_archive:{exc}"]
        return payload, 1

    payload["frame_count"] = int(frame_count)
    payload["pressure_source"] = pressure_source

    if args.frames is None:
        try:
            selected_frames = list(range(frame_count))
        except Exception as exc:
            payload["errors"] = [f"frame_selection:{exc}"]
            return payload, 1
    else:
        try:
            selected_frames = _parse_frame_spec(args.frames, frame_count)
        except Exception as exc:
            payload["errors"] = [f"frame_selection:{exc}"]
            return payload, 1

    payload["frame_indices"] = [int(frame) for frame in selected_frames]
    payload["selected_frames"] = [int(frame) for frame in selected_frames]
    payload["selected_frame_count"] = len(selected_frames)

    if frame_count == 0:
        payload["errors"] = ["empty_frame_series"]
        return payload, 1

    n = int(pressure_raw.shape[-1]) if pressure_raw.ndim >= 3 else 0
    if n <= 0:
        payload["errors"] = ["invalid_pressure_shape"]
        return payload, 1

    try:
        domain_length, domain_source = _resolve_domain_length(data, n, args.domain_length)
    except Exception as exc:
        payload["errors"] = [f"domain_length:{exc}"]
        return payload, 1

    payload["domain_length"] = float(domain_length)
    payload["domain_length_source"] = domain_source

    rows: list[dict[str, Any]] = []
    invalid = False
    for frame in selected_frames:
        row = _build_frame_row(data, frame, domain_length)
        rows.append(row)
        if row.get("status") not in {OK_STATUS, STATUS_NO_PROXY}:
            invalid = True
        if row.get("status") == STATUS_NO_PROXY:
            invalid = True

    payload["rows"] = rows

    valid_rows = [row for row in rows if row.get("status") == OK_STATUS and row.get("best_sign_proxy")]
    if valid_rows:
        first = valid_rows[0]
        payload["source_proxy_source"] = first.get("source_proxy_source")

    payload["aggregate_counts"] = {
        "selected_frame_count": len(selected_frames),
        "valid_frame_count": len(valid_rows),
        "minus_best_count": sum(1 for row in valid_rows if row["best_sign_proxy"]["sign"] == "minus"),
        "plus_best_count": sum(1 for row in valid_rows if row["best_sign_proxy"]["sign"] == "plus"),
    }
    payload["aggregate_metrics"] = _comparison_summary(rows)
    payload["sign_stability"] = _sign_stability(rows)
    payload["warnings"] = sorted(set(payload["warnings"]))

    if not valid_rows:
        payload["status"] = STATUS_NO_PROXY
        payload["errors"] = payload["errors"] or ["proxy_unavailable"]
        return payload, 1

    if invalid:
        payload["status"] = STATUS_MISSING_REQUIRED_FIELD
        payload["errors"] = payload["errors"] or ["one_or_more_frames_invalid"]
        return payload, 1

    payload["status"] = OK_STATUS
    payload["errors"] = []
    return payload, 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="raw pressure NPZ archive")
    parser.add_argument(
        "--frames",
        type=str,
        default=None,
        help="comma-separated frame list or ranges such as 0,2-4; defaults to all available frames",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="write the deterministic JSON report here",
    )
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON output")
    parser.add_argument(
        "--domain-length",
        type=float,
        default=None,
        help="override the periodic domain length when metadata is missing or needs checking",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload, code = _build_payload(args)
    text = _json_text(payload, args.pretty)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
