#!/usr/bin/env python3
"""Sharpen Calc 7 by scanning boundary delta1 and Bk across N128 snapshots."""

from __future__ import annotations

import argparse
import json
import math
import re
from pathlib import Path
import sys
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import scripts.ns_boundary_carrier_timeseries_diagnostic as carrier_diag
import scripts.ns_boundary_component_diagnostic as component_diag

SCRIPT_NAME = "scripts/ns_calc7_reynolds_boundary_scan.py"
CONTRACT = "ns_calc7_reynolds_boundary_scan"
DEFAULT_TIMESERIES_JSON = Path(
    "scripts/data/outputs/ns_boundary_carrier_timeseries_N128_20260618.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_calc7_reynolds_boundary_scan_N128_20260620.json"
)
DEFAULT_LAMBDA2_BAND = 1.0e-3

CONTROL_CARD = {
    "O": "Owner scans the Calc 7 N128 boundary carrier across snapshots and groups results by any available Reynolds-style label.",
    "R": "Track boundary delta1 = min g12 and min boundary Bk, while failing closed when Reynolds labels or frame-resolved Bk support are unavailable.",
    "C": SCRIPT_NAME,
    "S": "Existing carrier timeseries data give delta1 directly; boundary Bk is recomputed from the raw archive when available.",
    "L": "load timeseries -> infer labels -> optionally scan raw frames -> merge per-frame rows -> emit deterministic JSON",
    "P": "FAIL_CLOSED_CALC7_REYNOLDS_BOUNDARY_SCAN",
    "G": "This is empirical/non-promoting telemetry only; it does not discharge delta1, H_B, or Clay NS.",
    "F": "Residual gaps are missing Reynolds metadata, missing raw archive access, or missing boundary samples for a declared carrier frame.",
}

AUTHORITY = {
    "candidate_only": True,
    "clay_authority": False,
    "empirical_non_promoting": True,
    "promoted": False,
    "runtime_authority": False,
    "theorem_authority": False,
    "truth_authority": False,
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeseries-json", type=Path, default=DEFAULT_TIMESERIES_JSON)
    parser.add_argument("--raw-archive", type=Path, default=None)
    parser.add_argument("--lambda2-band", type=float, default=DEFAULT_LAMBDA2_BAND)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _infer_reynolds_label(*texts: str | None) -> dict[str, Any]:
    combined = " ".join(text for text in texts if isinstance(text, str))
    match = re.search(r"(?:^|[^A-Za-z])Re[_-]?(\d+(?:\.\d+)?)", combined)
    if match is None:
        return {
            "reynolds_label": None,
            "reynolds_value": None,
            "reynolds_label_available": False,
            "reynolds_label_unavailable": True,
            "source_text": combined,
        }
    value_text = match.group(1)
    return {
        "reynolds_label": f"Re{value_text}",
        "reynolds_value": float(value_text),
        "reynolds_label_available": True,
        "reynolds_label_unavailable": False,
        "source_text": combined,
    }


def _boundary_mask(lambda2: np.ndarray, beta: float, lambda2_band: float) -> tuple[np.ndarray, str]:
    mask = np.asarray(np.abs(lambda2) <= lambda2_band, dtype=bool)
    if np.any(mask):
        return mask, "absolute_lambda2_band"
    return np.asarray(lambda2 <= beta, dtype=bool), "beta_sublevel_fallback"


def _scan_bk_rows(
    raw_archive: Path,
    lambda2_band: float,
    frame_rows: dict[int, dict[str, Any]],
) -> tuple[dict[int, dict[str, Any]], list[str]]:
    warnings: list[str] = []
    scanned: dict[int, dict[str, Any]] = {}
    try:
        frame_sources, _ = carrier_diag._frame_sources(raw_archive, None)
    except Exception as exc:
        warnings.append(f"boundary_Bk_scan_skipped:{exc}")
        return scanned, warnings
    for source in frame_sources:
        frame = int(source.frame_index) if source.frame_index is not None else 0
        if frame not in frame_rows:
            continue
        row = frame_rows[frame]
        component_id = row.get("primary_carrier_id")
        if not isinstance(component_id, int) or component_id <= 0:
            scanned[frame] = {
                "boundary_bk_status": "missing_primary_carrier_id",
                "boundary_bk_min": None,
                "boundary_bk_mean": None,
                "boundary_bk_boundary_cell_count": 0,
                "boundary_bk_mask_source": None,
            }
            continue
        try:
            bundle, bundle_warnings = carrier_diag._optional_frame_bundle(
                source.data,
                source.frame_index,
                source.frame_count,
            )
            labels = component_diag._label_components(np.asarray(bundle.lambda2 <= bundle.beta, dtype=bool))
            boundary_mask, boundary_mask_source = _boundary_mask(bundle.lambda2, bundle.beta, lambda2_band)
            component_mask = labels == component_id
            component_boundary_mask = np.asarray(component_mask & boundary_mask, dtype=bool)
            if not np.any(component_boundary_mask):
                scanned[frame] = {
                    "boundary_bk_status": "no_boundary_samples_for_primary_carrier",
                    "boundary_bk_min": None,
                    "boundary_bk_mean": None,
                    "boundary_bk_boundary_cell_count": 0,
                    "boundary_bk_mask_source": boundary_mask_source,
                }
            else:
                boundary_bk = np.asarray(bundle.b_k[component_boundary_mask], dtype=np.float64)
                scanned[frame] = {
                    "boundary_bk_status": "ok",
                    "boundary_bk_min": float(np.min(boundary_bk)),
                    "boundary_bk_mean": float(np.mean(boundary_bk)),
                    "boundary_bk_boundary_cell_count": int(np.count_nonzero(component_boundary_mask)),
                    "boundary_bk_mask_source": boundary_mask_source,
                }
            warnings.extend(f"frame {frame}: {warning}" for warning in bundle_warnings)
        except Exception as exc:
            scanned[frame] = {
                "boundary_bk_status": f"scan_error:{exc}",
                "boundary_bk_min": None,
                "boundary_bk_mean": None,
                "boundary_bk_boundary_cell_count": 0,
                "boundary_bk_mask_source": None,
            }
    return scanned, warnings


def _finite_values(rows: list[dict[str, Any]], key: str) -> list[float]:
    values: list[float] = []
    for row in rows:
        value = row.get(key)
        if isinstance(value, (int, float)) and math.isfinite(float(value)):
            values.append(float(value))
    return values


def _build_payload(args: argparse.Namespace, timeseries: dict[str, Any]) -> dict[str, Any]:
    rows = timeseries.get("rows")
    if not isinstance(rows, list):
        raise ValueError("timeseries rows must be a list")

    raw_archive = args.raw_archive
    if raw_archive is None:
        input_value = timeseries.get("input")
        if isinstance(input_value, str):
            raw_archive = Path(input_value)

    frame_rows = {
        int(row["frame"]): row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("frame"), int)
    }
    dataset_label = Path(str(timeseries.get("input", ""))).name if timeseries.get("input") else "unknown_dataset"
    reynolds = _infer_reynolds_label(dataset_label, str(timeseries.get("input", "")))

    scanned_bk: dict[int, dict[str, Any]] = {}
    warnings: list[str] = []
    raw_archive_used = None
    if raw_archive is not None and raw_archive.exists():
        raw_archive_used = str(raw_archive)
        scanned_bk, warnings = _scan_bk_rows(raw_archive, args.lambda2_band, frame_rows)
    else:
        warnings.append("raw_archive_unavailable_boundary_Bk_scan_skipped")

    merged_rows: list[dict[str, Any]] = []
    for frame in sorted(frame_rows):
        row = dict(frame_rows[frame])
        row.update(scanned_bk.get(frame, {
            "boundary_bk_status": "raw_archive_unavailable",
            "boundary_bk_min": None,
            "boundary_bk_mean": None,
            "boundary_bk_boundary_cell_count": 0,
            "boundary_bk_mask_source": None,
        }))
        row["delta1_min"] = row.get("min_g12")
        row["dataset_label"] = dataset_label
        row["reynolds_label"] = reynolds["reynolds_label"]
        row["reynolds_value"] = reynolds["reynolds_value"]
        row["reynolds_label_available"] = reynolds["reynolds_label_available"]
        merged_rows.append(row)

    delta1_values = _finite_values(merged_rows, "delta1_min")
    bk_values = _finite_values(merged_rows, "boundary_bk_min")
    status = "ok"
    if not delta1_values:
        status = "error"
    elif not bk_values or not reynolds["reynolds_label_available"]:
        status = "degraded"

    return {
        "contract": CONTRACT,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "authority": AUTHORITY,
        "status": status,
        "timeseries_json": str(args.timeseries_json),
        "raw_archive_used": raw_archive_used,
        "lambda2_band": float(args.lambda2_band),
        "dataset": {
            "dataset_label": dataset_label,
            **reynolds,
        },
        "summary": {
            "frame_count": len(merged_rows),
            "delta1_min_global": min(delta1_values) if delta1_values else None,
            "delta1_max_global": max(delta1_values) if delta1_values else None,
            "boundary_bk_min_global": min(bk_values) if bk_values else None,
            "boundary_bk_max_global": max(bk_values) if bk_values else None,
            "ok_boundary_bk_rows": sum(row.get("boundary_bk_status") == "ok" for row in merged_rows),
            "reynolds_label_available": reynolds["reynolds_label_available"],
            "reynolds_label_unavailable": reynolds["reynolds_label_unavailable"],
        },
        "rows": merged_rows,
        "warnings": warnings,
        "errors": [],
    }


def main() -> int:
    args = _parse_args()
    timeseries = _load_json(args.timeseries_json)
    payload = _build_payload(args, timeseries)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if payload["status"] in {"ok", "degraded"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
