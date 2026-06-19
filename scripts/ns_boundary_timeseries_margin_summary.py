#!/usr/bin/env python3
"""Aggregate multiple per-frame boundary margin JSON files."""

from __future__ import annotations

import argparse
import json
import math
import re
from collections import Counter
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_boundary_timeseries_margin_summary.py"
CONTRACT = "ns_boundary_timeseries_margin_summary"
SCHEMA_VERSION = "1.0.0"
DEFAULT_OUTPUT = Path("outputs/ns_boundary_timeseries_margin_summary.json")

PASS_STATUS = {
    "ok",
    "pass",
    "passed",
    "success",
    "complete",
    "completed",
    "done",
    "closed",
}
FAIL_STATUS = {
    "fail",
    "failed",
    "error",
    "invalid",
    "blocked",
    "bad",
}
WARN_STATUS = {
    "warning",
    "warn",
    "partial",
    "missing",
}

FRAME_PATTERN = re.compile(r"(?i)(?:^|[._-])(?:frame|f|t)[_-]?(\d+)(?:$|[._-])")
COMPONENT_PATTERN = re.compile(r"(?i)(?:^|[._-])(?:component|comp|c)[_-]?(\d+)(?:$|[._-])")

FRAME_KEYS = (
    "frame",
    "frame_id",
    "frame_index",
    "frameIndex",
    "time_index",
    "index",
)
COMPONENT_KEYS = (
    "component",
    "component_id",
    "componentIndex",
    "component_index",
    "carrier_id",
    "carrier",
    "item",
    "item_id",
)

ROW_LIST_KEYS = ("rows", "items", "results", "entries", "frames", "components", "records")

DEFAULT_AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}
AUTHORITY_KEYS = tuple(DEFAULT_AUTHORITY.keys())


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "positional_inputs",
        nargs="*",
        help="Per-frame margin JSON paths.",
    )
    parser.add_argument(
        "--inputs",
        nargs="+",
        action="append",
        default=[],
        help="Additional per-frame margin JSON paths.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output JSON.")
    return parser.parse_args()


def _float_or_none(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        value = float(value)
    elif isinstance(value, str):
        try:
            value = float(value.strip())
        except ValueError:
            return None
    else:
        return None
    if not math.isfinite(value):
        return None
    return float(value)


def _int_or_none(value: Any) -> int | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value) if value.is_integer() else None
    if isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
        return int(parsed) if parsed.is_integer() else None
    return None


def _read_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _looks_like_row(value: Any) -> bool:
    if not isinstance(value, dict):
        return False
    row_keys = {"delta1", "mu", "status", "frame", "component", "component_id", "frame_id"}
    return bool(set(value).intersection(row_keys))


def _collect_rows(payload: Any, path: Path, warnings: list[str]) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    rows: list[tuple[dict[str, Any], dict[str, Any]]] = []
    if isinstance(payload, dict):
        if _looks_like_row(payload):
            return [(payload, {"source": "root"})]

        for key in ROW_LIST_KEYS:
            container = payload.get(key)
            if isinstance(container, list):
                for index, item in enumerate(container):
                    if isinstance(item, dict) and _looks_like_row(item):
                        rows.append((item, {"source": key, "source_index": index}))
                    elif isinstance(item, dict):
                        warnings.append(f"{path}:non-row-item:{key}:{index}")
                if rows:
                    return rows

        for key, value in payload.items():
            if key in {"authority", "metadata", "provenance", "notes", "warnings", "errors", "summary"}:
                continue
            if isinstance(value, dict) and _looks_like_row(value):
                rows.append((value, {"source": key}))
        if rows:
            return rows

        warnings.append(f"{path}:no-row-object-found")
        return []

    if isinstance(payload, list):
        for index, item in enumerate(payload):
            if isinstance(item, dict) and _looks_like_row(item):
                rows.append((item, {"source": "payload-list", "source_index": index}))
            elif isinstance(item, dict):
                warnings.append(f"{path}:non-row-item:payload-list:{index}")
        if rows:
            return rows

        warnings.append(f"{path}:list-payload-without-rows")
        return []

    warnings.append(f"{path}:payload-not-object-or-list")
    return []


def _extract_tree_field(payload: Any, keys: tuple[str, ...], depth: int = 4) -> Any | None:
    if depth < 0:
        return None
    if isinstance(payload, dict):
        for key in keys:
            if key in payload:
                return payload[key]
        for value in payload.values():
            if isinstance(value, (dict, list)):
                found = _extract_tree_field(value, keys, depth - 1)
                if found is not None:
                    return found
    elif isinstance(payload, list):
        for item in payload:
            if isinstance(item, (dict, list)):
                found = _extract_tree_field(item, keys, depth - 1)
                if found is not None:
                    return found
    return None


def _extract_metadata(payload: Any) -> dict[str, Any]:
    meta: dict[str, Any] = {}
    if not isinstance(payload, dict):
        return meta
    for key in ("metadata", "meta", "provenance", "source", "source_metadata", "info"):
        source = payload.get(key)
        if isinstance(source, dict):
            for meta_key, meta_value in source.items():
                if meta_key not in meta:
                    meta[meta_key] = meta_value
    return meta


def _infer_frame_component(
    row: dict[str, Any],
    *,
    metadata: dict[str, Any],
    path: Path,
) -> tuple[int | None, int | None]:
    frame = _int_or_none(_extract_tree_field(row, FRAME_KEYS))
    component = _int_or_none(_extract_tree_field(row, COMPONENT_KEYS))
    if frame is None:
        for key in FRAME_KEYS:
            frame = _int_or_none(metadata.get(key))
            if frame is not None:
                break
    if component is None:
        for key in COMPONENT_KEYS:
            component = _int_or_none(metadata.get(key))
            if component is not None:
                break

    if frame is None:
        for text in (path.name, path.stem, path.parent.name):
            match = FRAME_PATTERN.search(text.lower())
            if match is not None:
                frame = _int_or_none(match.group(1))
                if frame is not None:
                    break

    if component is None:
        for text in (path.name, path.stem, path.parent.name):
            match = COMPONENT_PATTERN.search(text.lower())
            if match is not None:
                component = _int_or_none(match.group(1))
                if component is not None:
                    break

    return frame, component


def _status_is_pass(raw_status: Any) -> tuple[str, bool]:
    if isinstance(raw_status, bool):
        return ("pass" if raw_status else "fail", bool(raw_status))
    if raw_status is None:
        return ("missing_status", False)
    if not isinstance(raw_status, str):
        return (f"non_string_status:{type(raw_status).__name__}", False)

    normalized = raw_status.strip().lower()
    if normalized in PASS_STATUS:
        return (normalized, True)
    if normalized in FAIL_STATUS or normalized in WARN_STATUS:
        return (normalized, False)
    return (f"unrecognized_status:{normalized}", False)


def _aggregate_stats(values: list[float]) -> dict[str, float | int | None]:
    if not values:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "mean": sum(values) / len(values),
    }


def _collect_authority(payload: Any) -> tuple[dict[str, bool], list[str], bool]:
    if not isinstance(payload, dict):
        return dict(DEFAULT_AUTHORITY), ["authority-payload-not-dict"], False

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        metadata = payload.get("metadata")
        authority = metadata.get("authority") if isinstance(metadata, dict) else None

    if authority is None:
        return dict(DEFAULT_AUTHORITY), ["authority-missing"], False

    observed = dict(DEFAULT_AUTHORITY)
    found_any = False
    warnings: list[str] = []
    valid = True
    for key, value in authority.items():
        if key in observed:
            found_any = True
            if isinstance(value, bool):
                observed[key] = value
            else:
                warnings.append(f"authority-{key}-non_bool:{type(value).__name__}")
                valid = False
                observed[key] = DEFAULT_AUTHORITY[key]

    for key in AUTHORITY_KEYS:
        if key not in authority:
            warnings.append(f"authority-{key}-missing")
            valid = False
            continue
        if observed[key] != DEFAULT_AUTHORITY[key]:
            warnings.append(f"authority-{key}-invalid:{observed[key]!r}")
            valid = False

    if not found_any:
        warnings.append("authority-not-found")
        valid = False

    return dict(observed), sorted(set(warnings)), bool(valid)


def _sorted_failing(items: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(
        items,
        key=lambda item: (
            str(item.get("path", "")),
            -1 if item.get("frame") is None else int(item["frame"]),
            -1 if item.get("component") is None else int(item["component"]),
            int(item.get("row_index", -1)),
        ),
    )


def _build_summary(input_paths: list[Path], output: Path) -> tuple[dict[str, Any], int]:
    warnings: list[str] = []
    status_counter: Counter[str] = Counter()
    delta1_values: list[float] = []
    mu_values: list[float] = []
    file_rows: list[dict[str, Any]] = []
    all_rows: list[dict[str, Any]] = []
    failing_items: list[dict[str, Any]] = []

    authority_samples: list[dict[str, bool]] = []
    authority_warnings: list[str] = []
    authority_all_valid = True
    file_read_errors = False

    for file_index, path in enumerate(input_paths):
        try:
            payload = _read_json(path)
        except FileNotFoundError:
            warnings.append(f"{path}:file_missing")
            file_rows.append({"path": str(path), "row_count": 0, "status": "missing", "file_index": file_index})
            authority_all_valid = False
            file_read_errors = True
            continue
        except json.JSONDecodeError as exc:
            warnings.append(f"{path}:invalid_json:{exc}")
            file_rows.append(
                {"path": str(path), "row_count": 0, "status": "invalid_json", "file_index": file_index}
            )
            authority_all_valid = False
            file_read_errors = True
            continue
        except OSError as exc:
            warnings.append(f"{path}:read_error:{exc}")
            file_rows.append({"path": str(path), "row_count": 0, "status": "read_error", "file_index": file_index})
            authority_all_valid = False
            file_read_errors = True
            continue

        if not isinstance(payload, (dict, list)):
            warnings.append(f"{path}:payload_not_object_or_list")
            file_rows.append({"path": str(path), "row_count": 0, "status": "bad_payload_type", "file_index": file_index})
            authority_all_valid = False
            file_read_errors = True
            continue

        metadata = _extract_metadata(payload)
        observed_authority, auth_warnings, auth_valid = _collect_authority(payload)
        authority_samples.append(observed_authority)
        authority_warnings.extend(auth_warnings)
        authority_all_valid = authority_all_valid and auth_valid

        rows = _collect_rows(payload, path, warnings)
        source_status = payload.get("status") if isinstance(payload, dict) else None
        source_status_text = "missing_status" if source_status is None else str(source_status)
        file_rows.append(
            {
                "path": str(path),
                "row_count": len(rows),
                "status": source_status_text,
                "contract": str(payload.get("contract")) if isinstance(payload, dict) else None,
                "script": str(payload.get("script")) if isinstance(payload, dict) else None,
                "file_index": file_index,
            }
        )

        for row_number, (row, row_context) in enumerate(rows, start=1):
            row_status = row.get("status", source_status)
            status_key, is_ok = _status_is_pass(row_status)
            status_counter[status_key] += 1

            row_metadata = _extract_metadata(row)
            merged_meta = dict(metadata)
            merged_meta.update(row_metadata)
            frame, component = _infer_frame_component(row, metadata=merged_meta, path=path)

            delta1 = _float_or_none(_extract_tree_field(row, ("delta1", "delta_1", "d1", "corrected_delta1")))
            if delta1 is None and isinstance(payload, dict):
                delta1 = _float_or_none(
                    _extract_tree_field(payload, ("delta1", "delta_1", "d1", "corrected_delta1"))
                )
            mu = _float_or_none(_extract_tree_field(row, ("mu", "mu_value", "u")))
            if mu is None and isinstance(payload, dict):
                mu = _float_or_none(_extract_tree_field(payload, ("mu", "mu_value", "u")))

            if delta1 is not None:
                delta1_values.append(delta1)
            if mu is not None:
                mu_values.append(mu)

            row_payload = {
                "path": str(path),
                "file_index": file_index,
                "row_in_file": row_number,
                "row_index": len(all_rows),
                "source": row_context,
                "frame": frame,
                "component": component,
                "status": row_status,
                "status_key": status_key,
                "delta1": delta1,
                "mu": mu,
            }
            all_rows.append(row_payload)

            reasons: list[str] = []
            if not is_ok:
                reasons.append(f"status={status_key}")
            if delta1 is None:
                reasons.append("missing_delta1")
            if mu is None:
                reasons.append("missing_mu")
            if (
                status_key == "missing_status"
                or status_key.startswith("non_string_status")
                or status_key.startswith("unrecognized_status")
            ):
                warnings.append(f"{path}:row-{row_number}:{status_key}")
            if isinstance(row.get("warnings"), list):
                for warning in row.get("warnings", []):
                    if isinstance(warning, str):
                        warnings.append(f"{path}:row-{row_number}:{warning}")

            if reasons:
                failing_items.append(
                    {
                        "path": str(path),
                        "file_index": file_index,
                        "row_index": len(all_rows),
                        "row_in_file": row_number,
                        "frame": frame,
                        "component": component,
                        "status": row_status,
                        "source": row_context,
                        "reasons": sorted(set(reasons)),
                    }
                )

    if not all_rows:
        warnings.append("no_rows_found")

    authority_observed = dict(DEFAULT_AUTHORITY)
    if authority_samples:
        for key in authority_observed:
            for sample in authority_samples:
                sample_value = sample.get(key)
                if sample_value != DEFAULT_AUTHORITY[key]:
                    authority_observed[key] = DEFAULT_AUTHORITY[key]
                    break
            else:
                authority_observed[key] = DEFAULT_AUTHORITY[key]

    status = "ok"
    if file_read_errors:
        status = "error"
    elif failing_items:
        status = "warning"
    elif warnings:
        status = "warning"

    status_reason = "ok" if status == "ok" else ("input_error" if status == "error" else "warnings_or_failures")

    status_counter_clean = dict(sorted(status_counter.items()))
    delta1_stats = _aggregate_stats(delta1_values)
    mu_stats = _aggregate_stats(mu_values)

    summary: dict[str, Any] = {
        "status": status,
        "status_reason": status_reason,
        "count": len(all_rows),
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "delta1": delta1_stats,
        "mu": mu_stats,
        "delta1_count": delta1_stats["count"],
        "delta1_min": delta1_stats["min"],
        "delta1_max": delta1_stats["max"],
        "delta1_mean": delta1_stats["mean"],
        "mu_count": mu_stats["count"],
        "mu_min": mu_stats["min"],
        "mu_max": mu_stats["max"],
        "mu_mean": mu_stats["mean"],
        "status_counts": status_counter_clean,
        "failing_items": _sorted_failing(failing_items),
        "warnings": sorted(set(warnings)),
        "authority": authority_observed,
        "authority_report": {
            "expected": DEFAULT_AUTHORITY,
            "observed_samples": authority_samples,
            "warnings": sorted(set(authority_warnings)),
            "valid": authority_all_valid,
            "files": file_rows,
        },
        "provenance": {
            "inputs": [str(path) for path in input_paths],
            "rows": all_rows,
            "row_count": len(all_rows),
            "file_count": len(file_rows),
        },
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "theorem_promoted": False,
        "clay_promoted": False,
        "proof_blocking": False,
        "O": "Aggregate per-frame corrected margin JSON artifacts for deterministic review.",
        "R": "Collect compatible delta1/mu JSONs, infer frame/component identity, and summarise bounds.",
        "C": SCRIPT_NAME,
        "S": "Frame/component inference is row-first, then metadata, then filename fallback.",
        "L": "Rows with non-pass status or missing delta1/mu are reported as failing items.",
        "P": "FAIL_CLOSED_BOUNDARY_TIMESERIES_MARGIN",
        "G": "No theorem, Clay, or promotion claim is made by this aggregator.",
        "F": "Promotion flags intentionally remain false.",
        "changed_files": [str(output)],
    }

    return summary, (1 if status == "error" else 0)


def main() -> int:
    args = _parse_args()
    input_paths = [Path(p) for p in args.positional_inputs]
    for block in args.inputs:
        for path_text in block:
            input_paths.append(Path(path_text))

    if not input_paths:
        print("error: provide at least one JSON input (positional args or --inputs)", flush=True)
        return 2

    summary, code = _build_summary(input_paths, args.output)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        if args.pretty:
            json.dump(summary, handle, sort_keys=True, indent=2, ensure_ascii=False)
        else:
            json.dump(summary, handle, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

    print(f"written: {args.output}")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
