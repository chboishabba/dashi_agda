#!/usr/bin/env python3
"""Summarize Calc 8 layer-L2 vorticity-fraction telemetry.

The script reads a Calc 8 JSON payload, groups rows by epsilon band, computes
per-band min/mean/max fraction statistics across frames, checks whether any
band crosses the 5% and 25% heuristic thresholds, and writes a deterministic
summary JSON beside the input unless an explicit output path is supplied.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_layer_l2_vorticity_fraction_summary.py"
CONTRACT = "ns_layer_l2_vorticity_fraction_summary"
SCHEMA_VERSION = "1.0.0"
DEFAULT_THRESHOLD_5 = 0.05
DEFAULT_THRESHOLD_25 = 0.25
DEFAULT_ROUTE_NAME = "Shahmurov/SerrinFromQ2Control"

ROW_CONTAINER_KEYS = ("rows", "items", "results", "entries", "frames", "records")
EPS_KEYS = ("eps", "epsilon", "eps_band", "epsBand", "band", "lambda2_band")
FRAME_KEYS = ("frame", "frame_id", "frameIndex", "frame_index", "index", "time_index")
FRACTION_KEYS = (
    "vorticity_fraction",
    "layer_fraction",
    "omega_fraction",
    "trace_fraction",
    "support_fraction",
    "fraction",
    "fraction_value",
    "alpha_omega_sq",
    "alpha_strain_sq",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", type=Path, help="Calc 8 JSON input path.")
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional summary output path. Defaults to a sibling *_summary.json file.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the output JSON.")
    return parser.parse_args()


def _read_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    if pretty:
        text = json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    path.write_text(text, encoding="utf-8")


def _is_finite_number(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    if isinstance(value, (int, float)):
        return math.isfinite(float(value))
    if isinstance(value, str):
        try:
            return math.isfinite(float(value.strip()))
        except ValueError:
            return False
    return False


def _float_or_none(value: Any) -> float | None:
    if not _is_finite_number(value):
        return None
    return float(value)


def _int_or_none(value: Any) -> int | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value) if value.is_integer() and math.isfinite(value) else None
    if isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
        return int(parsed) if parsed.is_integer() and math.isfinite(parsed) else None
    return None


def _extract_metadata(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        return {}
    for key in ("metadata", "meta", "provenance", "source", "info"):
        value = payload.get(key)
        if isinstance(value, dict):
            return value
    return {}


def _looks_like_row(value: Any) -> bool:
    if not isinstance(value, dict):
        return False
    if any(key in value for key in FRACTION_KEYS):
        return True
    if any(key in value for key in EPS_KEYS):
        return True
    if any(key in value for key in FRAME_KEYS):
        return True
    return False


def _collect_rows(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, list):
        return [item for item in payload if _looks_like_row(item)]
    if isinstance(payload, dict):
        for key in ROW_CONTAINER_KEYS:
            container = payload.get(key)
            if isinstance(container, list):
                rows = []
                for item in container:
                    if isinstance(item, dict) and isinstance(item.get("eps_rows"), list):
                        frame = item.get("frame")
                        source_path = item.get("source_path")
                        for eps_row in item["eps_rows"]:
                            if not isinstance(eps_row, dict):
                                continue
                            flat_row = dict(eps_row)
                            if frame is not None:
                                flat_row.setdefault("frame", frame)
                            if source_path is not None:
                                flat_row.setdefault("source_path", source_path)
                            if "fraction_of_total_omega_norm_sq" in flat_row:
                                flat_row.setdefault(
                                    "vorticity_fraction",
                                    flat_row["fraction_of_total_omega_norm_sq"],
                                )
                            rows.append(flat_row)
                    elif _looks_like_row(item):
                        rows.append(item)
                if rows:
                    return rows
        if _looks_like_row(payload):
            return [payload]
        for value in payload.values():
            if isinstance(value, dict) and _looks_like_row(value):
                return [value]
    return []


def _extract_first_number(payload: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        if key in payload:
            value = _float_or_none(payload[key])
            if value is not None:
                return value
    return None


def _extract_frame(payload: dict[str, Any], metadata: dict[str, Any]) -> int | None:
    frame = _extract_first_number(payload, FRAME_KEYS)
    if frame is not None:
        return int(frame)
    value = _extract_first_number(metadata, FRAME_KEYS)
    if value is not None:
        return int(value)
    return None


def _extract_eps(payload: dict[str, Any], metadata: dict[str, Any]) -> float | None:
    eps = _extract_first_number(payload, EPS_KEYS)
    if eps is not None:
        return eps
    return _extract_first_number(metadata, EPS_KEYS)


def _extract_fraction_key(payload: dict[str, Any]) -> str | None:
    for key in FRACTION_KEYS:
        if key in payload and _float_or_none(payload[key]) is not None:
            return key
    for key, value in payload.items():
        if "fraction" in key.lower() and _float_or_none(value) is not None:
            return key
    return None


def _extract_fraction(payload: dict[str, Any]) -> tuple[str | None, float | None]:
    key = _extract_fraction_key(payload)
    if key is None:
        return None, None
    return key, _float_or_none(payload.get(key))


def _stats(values: list[float]) -> dict[str, float | int | None]:
    if not values:
        return {"count": 0, "min": None, "mean": None, "max": None}
    return {
        "count": len(values),
        "min": min(values),
        "mean": sum(values) / len(values),
        "max": max(values),
    }


def _threshold_flags(min_value: float | None, max_value: float | None, threshold: float) -> dict[str, Any]:
    if min_value is None or max_value is None:
        return {"crosses": False, "touches": False}
    crosses = min_value < threshold < max_value
    touches = min_value <= threshold <= max_value
    return {"crosses": crosses, "touches": touches}


def _group_rows(rows: list[dict[str, Any]]) -> tuple[dict[float, list[dict[str, Any]]], list[str]]:
    grouped: dict[float, list[dict[str, Any]]] = defaultdict(list)
    warnings: list[str] = []
    for index, row in enumerate(rows):
        metadata = _extract_metadata(row)
        eps = _extract_eps(row, metadata)
        if eps is None:
            warnings.append(f"row[{index}]:missing_eps")
            continue
        grouped[float(eps)].append(row)
    return grouped, warnings


def _summarize_group(eps: float, rows: list[dict[str, Any]]) -> dict[str, Any]:
    fractions: list[float] = []
    frame_values: list[int] = []
    fraction_key_counts: dict[str, int] = defaultdict(int)
    for row in rows:
        metadata = _extract_metadata(row)
        frame = _extract_frame(row, metadata)
        if frame is not None:
            frame_values.append(frame)
        fraction_key, fraction = _extract_fraction(row)
        if fraction_key is not None:
            fraction_key_counts[fraction_key] += 1
        if fraction is not None:
            fractions.append(fraction)

    fraction_stats = _stats(fractions)
    band_summary = {
        "eps": eps,
        "frame_count": len(rows),
        "frame_min": min(frame_values) if frame_values else None,
        "frame_max": max(frame_values) if frame_values else None,
        "fraction_field": max(fraction_key_counts, key=fraction_key_counts.get) if fraction_key_counts else None,
        "fraction_count": len(fractions),
        "fraction_stats": fraction_stats,
        "crosses_5pct": _threshold_flags(fraction_stats["min"], fraction_stats["max"], DEFAULT_THRESHOLD_5)[
            "crosses"
        ],
        "crosses_25pct": _threshold_flags(fraction_stats["min"], fraction_stats["max"], DEFAULT_THRESHOLD_25)[
            "crosses"
        ],
        "touches_5pct": _threshold_flags(fraction_stats["min"], fraction_stats["max"], DEFAULT_THRESHOLD_5)[
            "touches"
        ],
        "touches_25pct": _threshold_flags(fraction_stats["min"], fraction_stats["max"], DEFAULT_THRESHOLD_25)[
            "touches"
        ],
    }
    return band_summary


def _route_implication(any_5: bool, any_25: bool) -> tuple[str, str]:
    if any_25:
        return (
            "25pct_crossed",
            "At least one epsilon band spans the 25% heuristic threshold, so the Serrin route stays evidence-bearing but not promoted.",
        )
    if any_5:
        return (
            "5pct_crossed",
            "At least one epsilon band spans the 5% heuristic threshold, so the Serrin route has a visible signal but remains non-promoting.",
        )
    return (
        "below_5pct",
        "No epsilon band crosses the 5% heuristic threshold, so the Serrin route remains only a weak empirical gate.",
    )


def build_summary(input_path: Path) -> tuple[dict[str, Any], list[str]]:
    payload = _read_json(input_path)
    warnings: list[str] = []
    rows = _collect_rows(payload)
    metadata = _extract_metadata(payload)
    all_fraction_values: list[float] = []
    fraction_field_counts: dict[str, int] = defaultdict(int)

    if not rows:
        raise ValueError(f"no row-like records found in {input_path}")

    grouped, group_warnings = _group_rows(rows)
    warnings.extend(group_warnings)
    if not grouped:
        raise ValueError(f"no epsilon bands found in {input_path}")

    for row in rows:
        fraction_key, fraction = _extract_fraction(row)
        if fraction_key is not None:
            fraction_field_counts[fraction_key] += 1
        if fraction is not None:
            all_fraction_values.append(fraction)
        elif any(key in row for key in FRACTION_KEYS):
            warnings.append("row:non_numeric_fraction")
        else:
            warnings.append("row:missing_fraction")

    band_summaries = [_summarize_group(eps, grouped[eps]) for eps in sorted(grouped)]
    if not all_fraction_values:
        raise ValueError(f"no numeric fraction samples found in {input_path}")
    any_5 = any(item["crosses_5pct"] for item in band_summaries)
    any_25 = any(item["crosses_25pct"] for item in band_summaries)
    implication_code, implication_text = _route_implication(any_5, any_25)

    frame_counts = [band["frame_count"] for band in band_summaries]

    summary = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "input": str(input_path),
        "status": "ok",
        "row_count": len(rows),
        "eps_band_count": len(band_summaries),
        "fraction_field": max(fraction_field_counts, key=fraction_field_counts.get) if fraction_field_counts else None,
        "fraction_field_counts": dict(sorted(fraction_field_counts.items())),
        "thresholds": {
            "five_percent": DEFAULT_THRESHOLD_5,
            "twenty_five_percent": DEFAULT_THRESHOLD_25,
        },
        "route": {
            "name": DEFAULT_ROUTE_NAME,
            "implication_code": implication_code,
            "implication": implication_text,
            "any_band_crosses_5pct": any_5,
            "any_band_crosses_25pct": any_25,
        },
        "eps_bands": band_summaries,
        "frame_count_stats": _stats([float(value) for value in frame_counts]),
        "fraction_overall_stats": _stats(all_fraction_values),
        "warnings": sorted(set(warnings)),
        "authority": {
            "candidate_only": bool(metadata.get("candidate_only", True)),
            "empirical_non_promoting": bool(metadata.get("empirical_non_promoting", True)),
            "promoted": bool(metadata.get("promoted", False)),
            "truth_authority": bool(metadata.get("truth_authority", False)),
            "theorem_authority": bool(metadata.get("theorem_authority", False)),
            "clay_authority": bool(metadata.get("clay_authority", False)),
            "runtime_authority": bool(metadata.get("runtime_authority", False)),
        },
        "O": "Summarize Calc 8 layer-L2 vorticity-fraction telemetry for the Shahmurov/SerrinFromQ2Control route.",
        "R": "Compute per-eps fraction aggregates and flag whether the empirical bands cross the 5% and 25% heuristics.",
        "C": SCRIPT_NAME,
        "S": "Group Calc 8 rows by epsilon band, summarize fraction ranges across frames, and keep the output deterministic.",
        "L": "The route stays evidence-only; crossing 25% is a stronger empirical signal than crossing 5%, but neither is a theorem.",
        "P": "FAIL_CLOSED_NS_LAYER_L2_VORTICITY_FRACTION_SUMMARY",
        "G": "Do not promote SerrinFromQ2Control or Clay claims from this telemetry alone.",
        "F": "Analytic proof obligations remain open; the fractions are only heuristic route indicators.",
    }
    return summary, warnings


def main() -> int:
    args = _parse_args()
    output_path = args.output
    if output_path is None:
        output_path = args.input_json.with_name(f"{args.input_json.stem}_summary.json")

    summary, warnings = build_summary(args.input_json)
    if warnings:
        summary["warnings"] = sorted(set(summary.get("warnings", [])) | set(warnings))
        summary["status"] = "warning"

    output_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(output_path, summary, args.pretty)
    print(f"written: {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
