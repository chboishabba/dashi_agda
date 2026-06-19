#!/usr/bin/env python3
"""Regression checker for signed-region partition JSON outputs."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Iterable


SCRIPT_NAME = "scripts/check_ns_lambda2_signed_region_partition_regression.py"
CONTRACT = "check_ns_lambda2_signed_region_partition_regression"
OK_STATUS = "ok"
ERROR_STATUS = "error"
EXPECTED_FRAME_COUNT = 13
TOLERANCE = 1e-6

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
REQUIRED_REGION_LABELS = (
    "lambda2_lt_-10",
    "lambda2_-10_to_-3",
    "lambda2_-3_to_-1",
    "lambda2_-1_to_-0.1",
    "lambda2_-0.1_to_0.1",
    "lambda2_0.1_to_1",
    "lambda2_1_to_3",
    "lambda2_3_to_10",
    "lambda2_gt_10",
    "lambda2_negative_total",
    "lambda2_near_zero_total",
    "lambda2_positive_total",
)
PARTITION_REGION_LABELS = (
    "lambda2_lt_-10",
    "lambda2_-10_to_-3",
    "lambda2_-3_to_-1",
    "lambda2_-1_to_-0.1",
    "lambda2_-0.1_to_0.1",
    "lambda2_0.1_to_1",
    "lambda2_1_to_3",
    "lambda2_3_to_10",
    "lambda2_gt_10",
)
REGION_LABEL_ALIASES = {label: {label} for label in REQUIRED_REGION_LABELS}
REGION_CONTAINER_KEYS = (
    "regions",
    "region_fractions",
    "partition",
    "signed_region_partition",
    "signed_regions",
    "region_partition",
)
FRAME_CONTAINER_KEYS = ("frames", "rows", "entries", "results", "records")
FRAME_COUNT_KEYS = (
    "frame_count",
    "available_frame_count",
    "processed_frame_count",
    "ok_frame_count",
    "selected_frame_count",
)
AGGREGATE_KEYS = ("aggregate_stats", "aggregate", "summary", "stats")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "partition_json",
        type=Path,
        help="Path to the signed-region partition JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=None,
        help="Optional path for writing the compact regression status JSON.",
    )
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n",
        encoding="utf-8",
    )


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _join_path(path: tuple[Any, ...]) -> str:
    if not path:
        return ""
    pieces: list[str] = []
    for entry in path:
        if isinstance(entry, int):
            if pieces:
                pieces[-1] += f"[{entry}]"
            else:
                pieces.append(f"[{entry}]")
            continue
        pieces.append(str(entry))
    return ".".join(pieces)


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    errors.append(f"{prefix}: {message}" if prefix else message)


def _record_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    warnings.append(f"{prefix}: {message}" if prefix else message)


def _coerce_finite_float(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        value_f = float(value)
    elif isinstance(value, str):
        try:
            value_f = float(value.strip())
        except ValueError:
            return None
    else:
        return None
    if not math.isfinite(value_f):
        return None
    return value_f


def _get_by_alias(payload: dict[str, Any], aliases: Iterable[str]) -> tuple[str | None, Any | None]:
    alias_list = tuple(aliases)
    for alias in alias_list:
        if alias in payload:
            return alias, payload[alias]
    normalized_aliases = {_normalize_key(alias): alias for alias in alias_list}
    for key, value in payload.items():
        if isinstance(key, str) and _normalize_key(key) in normalized_aliases:
            return key, value
    return None, None


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"missing required control-card field {key!r}")


def _check_status(payload: dict[str, Any], errors: list[str]) -> None:
    status = payload.get("status")
    if not isinstance(status, str) or not status.strip():
        errors.append("status must be a non-empty string")
    elif status != OK_STATUS:
        errors.append(f"status must be {OK_STATUS!r}, got {status!r}")


def _check_authority_flags(node: Any, errors: list[str], path: tuple[Any, ...]) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            if isinstance(key, str):
                normalized = _normalize_key(key)
                if normalized in {"candidateonly", "empiricalnonpromoting", "nonpromoting", "diagnosticonly"}:
                    _check_authority_flags(value, errors, path + (key,))
                    continue
                if (
                    ("promotion" in normalized or "promoting" in normalized or "promoted" in normalized)
                    and isinstance(value, bool)
                    and value
                ):
                    _record_error(errors, path + (key,), "must be false")
                if normalized in {"clayauthority", "theoremauthority", "runtimeauthority", "truthauthority"}:
                    if isinstance(value, bool) and value:
                        _record_error(errors, path + (key,), "must be false")
            _check_authority_flags(value, errors, path + (key,))
    elif isinstance(node, list):
        for index, value in enumerate(node):
            _check_authority_flags(value, errors, path + (index,))


def _require_authority_object(payload: dict[str, Any], errors: list[str]) -> dict[str, Any] | None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("missing authority object")
        return None
    if not authority:
        errors.append("authority object must not be empty")
        return None
    return authority


def _find_frame_container(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in FRAME_CONTAINER_KEYS:
        container = payload.get(key)
        if isinstance(container, list):
            return [item for item in container if isinstance(item, dict)]
    return []


def _extract_frame_index(frame: dict[str, Any], fallback: int) -> int:
    for key in ("frame", "frame_index", "frameIndex", "index", "time_index"):
        value = frame.get(key)
        if isinstance(value, int) and not isinstance(value, bool):
            return value
        if isinstance(value, str):
            try:
                parsed = int(value.strip())
            except ValueError:
                continue
            return parsed
    return fallback


def _is_region_label_alias(label: str, canonical: str) -> bool:
    normalized = _normalize_key(label)
    return normalized in {_normalize_key(alias) for alias in REGION_LABEL_ALIASES[canonical]}


def _canonical_region_label(label: str) -> str | None:
    for canonical in REQUIRED_REGION_LABELS:
        if _is_region_label_alias(label, canonical):
            return canonical
    return None


def _extract_region_entries(frame: dict[str, Any]) -> tuple[str | None, list[dict[str, Any]]]:
    for key in REGION_CONTAINER_KEYS:
        container = frame.get(key)
        if isinstance(container, dict):
            entries: list[dict[str, Any]] = []
            for label, value in container.items():
                entries.append({"label": label, "fraction": value})
            return key, entries
        if isinstance(container, list):
            entries = [item for item in container if isinstance(item, dict)]
            return key, entries
    return None, []


def _extract_entry_label(entry: dict[str, Any]) -> str | None:
    for key in ("label", "region", "name", "kind", "tag", "bucket", "phase"):
        value = entry.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None


def _extract_entry_fraction(entry: dict[str, Any]) -> float | None:
    for key in (
        "fraction",
        "region_fraction",
        "partition_fraction",
        "value",
        "weight",
        "mass_fraction",
    ):
        if key in entry:
            return _coerce_finite_float(entry[key])
    numeric_values = []
    for value in entry.values():
        coerced = _coerce_finite_float(value)
        if coerced is not None:
            numeric_values.append(coerced)
    if len(numeric_values) == 1:
        return numeric_values[0]
    return None


def _find_aggregate_stats(payload: dict[str, Any]) -> tuple[str | None, dict[str, Any] | None]:
    for key in AGGREGATE_KEYS:
        value = payload.get(key)
        if isinstance(value, dict):
            return key, value
    return None, None


def _collect_frame_counts(payload: dict[str, Any]) -> list[int]:
    values: list[int] = []
    for key in FRAME_COUNT_KEYS:
        value = payload.get(key)
        if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
            values.append(value)
    return values


def _validate_frames(
    payload: dict[str, Any],
    errors: list[str],
    warnings: list[str],
) -> dict[str, Any]:
    frames = _find_frame_container(payload)
    if not frames:
        _record_error(errors, ("frames",), "missing frame container")
        return {"frame_count": 0, "labels_seen": [], "max_abs_sum_error": None}

    if len(frames) != EXPECTED_FRAME_COUNT:
        _record_error(
            errors,
            ("frames",),
            f"must contain {EXPECTED_FRAME_COUNT} frames, got {len(frames)}",
        )

    labels_seen: set[str] = set()
    per_frame_sum_errors: list[float] = []
    region_fraction_count = 0

    for index, frame in enumerate(frames):
        frame_index = _extract_frame_index(frame, index)
        status = frame.get("status")
        if isinstance(status, str) and status.strip() and status != OK_STATUS:
            _record_error(errors, ("frames", index, "status"), f"must be {OK_STATUS!r}, got {status!r}")

        container_key, region_entries = _extract_region_entries(frame)
        if container_key is None:
            _record_error(errors, ("frames", index), "missing region partition data")
            continue
        if not region_entries:
            _record_error(errors, ("frames", index, container_key), "must contain at least one region entry")
            continue

        frame_fraction_total = 0.0
        frame_labels: set[str] = set()

        for entry_index, entry in enumerate(region_entries):
            label = _extract_entry_label(entry)
            if label is None:
                _record_error(errors, ("frames", index, container_key, entry_index), "missing region label")
                continue
            canonical_label = _canonical_region_label(label)
            if canonical_label is None:
                frame_labels.add(label)
            else:
                frame_labels.add(canonical_label)
                labels_seen.add(canonical_label)

            fraction = _extract_entry_fraction(entry)
            if fraction is None:
                _record_error(
                    errors,
                    ("frames", index, container_key, entry_index),
                    f"region {label!r} fraction must be finite numeric",
                )
                continue
            if fraction < 0.0 or fraction > 1.0:
                _record_error(
                    errors,
                    ("frames", index, container_key, entry_index),
                    f"region {label!r} fraction must be in [0, 1], got {fraction!r}",
                )
            if canonical_label in PARTITION_REGION_LABELS:
                frame_fraction_total += fraction
            region_fraction_count += 1

        missing_labels = [label for label in REQUIRED_REGION_LABELS if label not in frame_labels]
        if missing_labels:
            _record_error(
                errors,
                ("frames", index, container_key),
                f"missing required region labels: {', '.join(missing_labels)}",
            )

        partition_fraction_sum = _coerce_finite_float(frame.get("partition_fraction_sum"))
        if partition_fraction_sum is not None:
            frame_fraction_total = partition_fraction_sum
        sum_error = abs(frame_fraction_total - 1.0)
        per_frame_sum_errors.append(sum_error)
        if not math.isfinite(frame_fraction_total):
            _record_error(errors, ("frames", index, container_key), "region fractions must sum to a finite value")
        elif sum_error > TOLERANCE:
            _record_error(
                errors,
                ("frames", index, container_key),
                f"region fractions must sum to 1 within {TOLERANCE:g}; got {frame_fraction_total:.17g}",
            )

        if frame_index != index:
            _record_warning(
                warnings,
                ("frames", index, "frame"),
                f"frame index {frame_index} does not match positional index {index}",
            )

    return {
        "frame_count": len(frames),
        "labels_seen": sorted(labels_seen),
        "region_fraction_count": region_fraction_count,
        "max_abs_sum_error": max(per_frame_sum_errors) if per_frame_sum_errors else None,
    }


def _validate_aggregate_stats(
    payload: dict[str, Any],
    errors: list[str],
) -> dict[str, Any]:
    aggregate_key, aggregate = _find_aggregate_stats(payload)
    if aggregate_key is None or aggregate is None:
        errors.append("missing aggregate stats object")
        return {"present": False, "keys": []}
    if not aggregate:
        errors.append(f"{aggregate_key} object must not be empty")
        return {"present": True, "keys": []}

    finite_numeric_keys: list[str] = []
    for key, value in aggregate.items():
        if isinstance(value, dict):
            continue
        if isinstance(value, list):
            continue
        if isinstance(value, bool) or value is None:
            continue
        if isinstance(value, (int, float, str)):
            coerced = _coerce_finite_float(value)
            if coerced is not None:
                finite_numeric_keys.append(str(key))
                if 0.0 <= coerced <= 1.0 and "fraction" in _normalize_key(str(key)):
                    continue
        # Non-numeric aggregate fields are allowed, but a completely string-only
        # aggregate object would not satisfy the regression contract.

    if not finite_numeric_keys:
        errors.append(f"{aggregate_key} must contain at least one finite numeric statistic")

    return {"present": True, "keys": sorted(str(key) for key in aggregate.keys())}


def _build_result(
    payload: dict[str, Any],
    partition_path: Path,
    output_json: Path | None,
) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_control_card(payload, errors)
    _check_status(payload, errors)
    _require_authority_object(payload, errors)
    _check_authority_flags(payload, errors, ())

    frame_count_values = _collect_frame_counts(payload)
    if frame_count_values and any(value != EXPECTED_FRAME_COUNT for value in frame_count_values):
        for key in FRAME_COUNT_KEYS:
            value = payload.get(key)
            if isinstance(value, int) and not isinstance(value, bool) and value != EXPECTED_FRAME_COUNT:
                _record_error(errors, (key,), f"must be {EXPECTED_FRAME_COUNT}, got {value}")
    if not frame_count_values:
        warnings.append("no explicit frame-count field found; relying on frame container length")

    frame_summary = _validate_frames(payload, errors, warnings)
    aggregate_summary = _validate_aggregate_stats(payload, errors)

    status = OK_STATUS if not errors else ERROR_STATUS
    result = {
        "contract": CONTRACT,
        "status": status,
        "errors": errors,
        "warnings": warnings,
        "inputs": {"partition_json": str(partition_path), "output_json": str(output_json) if output_json else None},
        "expected_frame_count": EXPECTED_FRAME_COUNT,
        "validation": {
            **frame_summary,
            **aggregate_summary,
        },
        "O": "Validate signed-region partition regression JSON.",
        "R": "Check frame coverage, region labels, fraction bounds, sum-to-one behavior, and authority flags.",
        "C": SCRIPT_NAME,
        "S": "Fail closed when the partition payload violates the recorded regression contract.",
        "L": "Status is ok only when all required frames, labels, and fraction invariants hold.",
        "P": "FAIL_CLOSED_NS_LAMBDA2_SIGNED_REGION_PARTITION_REGRESSION",
        "G": "No theorem, Clay, or promotion authority is inferred by this checker.",
        "F": "This checker only validates empirical partition telemetry and emits a compact status record.",
        "changed_files": [str(partition_path)] + ([str(output_json)] if output_json else []),
    }
    return result


def main() -> int:
    try:
        args = _parse_args()
        payload = _load_json(args.partition_json)
        result = _build_result(payload, args.partition_json, args.output_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"partition_json": None, "output_json": None},
            "expected_frame_count": EXPECTED_FRAME_COUNT,
            "validation": {"frame_count": 0, "labels_seen": [], "present": False, "keys": []},
            "O": "Validate signed-region partition regression JSON.",
            "R": "Check frame coverage, region labels, fraction bounds, sum-to-one behavior, and authority flags.",
            "C": SCRIPT_NAME,
            "S": "Fail closed when the partition payload violates the recorded regression contract.",
            "L": "Status is ok only when all required frames, labels, and fraction invariants hold.",
            "P": "FAIL_CLOSED_NS_LAMBDA2_SIGNED_REGION_PARTITION_REGRESSION",
            "G": "No theorem, Clay, or promotion authority is inferred by this checker.",
            "F": "This checker only validates empirical partition telemetry and emits a compact status record.",
            "changed_files": [],
        }
        print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
        return 1

    if args.output_json is not None:
        _write_json(args.output_json, result)
    print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
    return 0 if result["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
