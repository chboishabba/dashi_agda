#!/usr/bin/env python3
"""Validate the JSON emitted by ns_triad_kn_external_wall1_csv_ingest."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_kn_external_wall1_csv_ingest.py"
CONTRACT = "check_ns_triad_kn_external_wall1_csv_ingest"
SOURCE_CONTRACT = "ns_triad_kn_external_wall1_csv_ingest"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_kn_external_wall1_csv_ingest.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EXTERNAL_WALL1_CSV_INGEST"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EXTERNAL_WALL1_CSV_INGEST_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_INPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_external_wall1_csv_ingest_20260623.json"
)

EXPECTED_TOP_LEVEL_FLAGS = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "theorem_promoted": False,
    "clay_promoted": False,
}

OPTIONAL_CSV_KEYS = (
    "csv",
    "csv_path",
    "source_csv",
    "input_csv",
    "path",
    "file",
    "filename",
)

SUMMARY_KEYS = (
    "row_count",
    "rows",
    "row_total",
    "total_rows",
    "data_row_count",
    "csv_row_count",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("payload must be object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _string(value: Any) -> str | None:
    if isinstance(value, str) and value.strip():
        return value
    return None


def _first_present(payload: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in payload:
            return payload[key]
    return None


def _canonical_summary_object(payload: dict[str, Any]) -> dict[str, Any] | None:
    for key in ("canonical_summary", "summary"):
        value = payload.get(key)
        if isinstance(value, dict):
            return value
    return None


def _check_flag(payload: dict[str, Any], key: str, expected: bool, errors: list[str], path: str = "") -> None:
    value = payload.get(key)
    if value is not expected:
        label = f"{path}.{key}" if path else key
        errors.append(f"{label}: must be {expected!r}")


def _load_file_summaries(payload: dict[str, Any], errors: list[str]) -> list[dict[str, Any]]:
    for key in ("file_summaries", "summaries", "files", "input_files", "input_summaries"):
        value = payload.get(key)
        if value is None:
            continue
        if not isinstance(value, list):
            errors.append(f"{key}: must be list")
            return []
        summaries: list[dict[str, Any]] = []
        for index, item in enumerate(value):
            if not isinstance(item, dict):
                errors.append(f"{key}[{index}]: must be object")
                continue
            summaries.append(item)
        return summaries
    errors.append("file_summaries: must be present")
    return []


def _summary_path(summary: dict[str, Any]) -> str | None:
    for key in OPTIONAL_CSV_KEYS:
        value = summary.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None


def _summary_present(summary: dict[str, Any]) -> bool:
    for key in ("present", "exists", "summarized", "included"):
        value = summary.get(key)
        if isinstance(value, bool):
            return value
    if _summary_path(summary) is not None:
        return True
    return False


def _summary_row_count(summary: dict[str, Any]) -> int | None:
    counts = [summary.get(key) for key in SUMMARY_KEYS if key in summary]
    parsed: list[int] = []
    for value in counts:
        if value is None:
            continue
        count = _nonnegative_int(value)
        if count is None:
            return None
        parsed.append(count)
    if not parsed:
        return None
    if len(set(parsed)) > 1:
        return None
    return parsed[0]


def _check_summary(summary: dict[str, Any], index: int, errors: list[str], warnings: list[str]) -> tuple[bool, int]:
    path = f"file_summaries[{index}]"
    summary_path = _summary_path(summary)
    present = _summary_present(summary)

    if summary_path is None and not present:
        errors.append(f"{path}: must include a file path or an explicit presence flag")

    row_count = _summary_row_count(summary)
    if present:
        if row_count is None:
            errors.append(f"{path}: present input summaries must carry a nonnegative row count")
    else:
        if row_count is None:
            warnings.append(f"{path}: optional CSV is absent or unsummarized")
        elif row_count != 0:
            errors.append(f"{path}: absent optional CSVs must not report positive rows")

    if summary.get("candidate_only") is not True:
        errors.append(f"{path}.candidate_only: must be true")
    if summary.get("empirical_non_promoting") is not True:
        errors.append(f"{path}.empirical_non_promoting: must be true")
    if summary.get("theorem_promoted") is not False:
        errors.append(f"{path}.theorem_promoted: must be false")
    if summary.get("clay_promoted") is not False:
        errors.append(f"{path}.clay_promoted: must be false")

    canonical = _canonical_summary_object(summary)
    if canonical is not None:
        for key, expected in EXPECTED_TOP_LEVEL_FLAGS.items():
            if canonical.get(key) is not expected:
                errors.append(f"{path}.canonical_summary.{key}: must be {expected!r}")
        if canonical.get("theorem_promoted") is not False:
            errors.append(f"{path}.canonical_summary.theorem_promoted: must be false")
        if canonical.get("clay_promoted") is not False:
            errors.append(f"{path}.canonical_summary.clay_promoted: must be false")
        if canonical.get("row_count") is not None and _nonnegative_int(canonical.get("row_count")) is None:
            errors.append(f"{path}.canonical_summary.row_count: must be nonnegative int or null")
    elif "canonical_summary" in summary or "summary" in summary:
        errors.append(f"{path}.canonical_summary: must be object or null")

    return present, row_count or 0


def _check_artifact_handling(payload: dict[str, Any], errors: list[str]) -> None:
    artifact_present = any(
        bool(payload.get(key))
        for key in ("n6_artifact_present", "artifact_present", "has_n6_artifact")
    )
    if not artifact_present:
        for key in ("file_summaries", "summaries", "files", "input_files", "input_summaries"):
            summaries = payload.get(key)
            if not isinstance(summaries, list):
                continue
            for item in summaries:
                if not isinstance(item, dict):
                    continue
                artifact_marker = _first_present(item, "artifact_kind", "artifact_name", "dataset", "label")
                path = _summary_path(item)
                if (isinstance(artifact_marker, str) and "n6" in artifact_marker.lower()) or (
                    isinstance(path, str) and "n6" in path.lower()
                ):
                    artifact_present = True
                    break
            if artifact_present:
                break
    if not artifact_present:
        return

    handling = _first_present(payload, "artifact_handling", "artifact", "artifacts")
    if not isinstance(handling, dict):
        errors.append("artifact_handling: must be object when an N6 artifact is present")
        return

    for key in ("present", "handled", "recorded"):
        if key in handling and handling.get(key) is not True:
            errors.append(f"artifact_handling.{key}: must be true when an N6 artifact is present")
    if _string(handling.get("path")) is None and _string(handling.get("csv")) is None:
        errors.append("artifact_handling: must include a non-empty path when an N6 artifact is present")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("status") not in {OK_STATUS, ERROR_STATUS}:
        errors.append("status: must be ok|error")
    if not isinstance(payload.get("ok"), bool):
        errors.append("ok: must be bool")
    if not isinstance(payload.get("warnings"), list):
        errors.append("warnings: must be list")
    if not isinstance(payload.get("error_count"), int) or payload.get("error_count") < 0:
        errors.append("error_count: must be nonnegative int")

    for key, expected in EXPECTED_TOP_LEVEL_FLAGS.items():
        _check_flag(payload, key, expected, errors)

    authority = payload.get("authority")
    if authority is not None:
        if not isinstance(authority, dict):
            errors.append("authority: must be object or null")
        else:
            for key, expected in (
                ("candidate_only", True),
                ("empirical_non_promoting", True),
                ("theorem_promoted", False),
                ("clay_promoted", False),
            ):
                if authority.get(key) is not expected:
                    errors.append(f"authority.{key}: must be {expected!r}")

    summaries = _load_file_summaries(payload, errors)
    present_count = 0
    summarized_row_count = 0
    for index, summary in enumerate(summaries):
        present, row_count = _check_summary(summary, index, errors, warnings)
        if present:
            present_count += 1
            summarized_row_count += row_count

    if not summaries:
        errors.append("file_summaries: must contain at least one summary")
    elif present_count == 0:
        errors.append("file_summaries: at least one input file must be summarized")

    canonical = _canonical_summary_object(payload)
    if canonical is None:
        errors.append("canonical_summary: must be present as an object")
    else:
        for key, expected in EXPECTED_TOP_LEVEL_FLAGS.items():
            if canonical.get(key) is not expected:
                errors.append(f"canonical_summary.{key}: must be {expected!r}")
        if canonical.get("theorem_promoted") is not False:
            errors.append("canonical_summary.theorem_promoted: must be false")
        if canonical.get("clay_promoted") is not False:
            errors.append("canonical_summary.clay_promoted: must be false")
        if canonical.get("file_summary_count") is not None and _nonnegative_int(canonical.get("file_summary_count")) is None:
            errors.append("canonical_summary.file_summary_count: must be nonnegative int or null")
        if canonical.get("summarized_file_count") is not None and _nonnegative_int(canonical.get("summarized_file_count")) is None:
            errors.append("canonical_summary.summarized_file_count: must be nonnegative int or null")
        if canonical.get("row_count") is not None:
            canonical_row_count = _nonnegative_int(canonical.get("row_count"))
            if canonical_row_count is None:
                errors.append("canonical_summary.row_count: must be nonnegative int or null")
            elif present_count > 0 and canonical_row_count != summarized_row_count:
                errors.append("canonical_summary.row_count: must match summed summarized row counts")
        if canonical.get("summarized_file_count") is not None:
            canonical_file_count = _nonnegative_int(canonical.get("summarized_file_count"))
            if canonical_file_count is not None and canonical_file_count != present_count:
                errors.append("canonical_summary.summarized_file_count: must match summarized input files")

    for key in ("row_count", "total_row_count", "summed_row_count"):
        if key in payload and _nonnegative_int(payload.get(key)) is None:
            errors.append(f"{key}: must be nonnegative int or null")
    if _nonnegative_int(payload.get("row_count")) is not None and present_count > 0:
        if int(payload["row_count"]) != summarized_row_count:
            errors.append("row_count: must match the sum of summarized input rows")
    if _nonnegative_int(payload.get("total_row_count")) is not None and present_count > 0:
        if int(payload["total_row_count"]) != summarized_row_count:
            errors.append("total_row_count: must match the sum of summarized input rows")
    if _nonnegative_int(payload.get("summed_row_count")) is not None and present_count > 0:
        if int(payload["summed_row_count"]) != summarized_row_count:
            errors.append("summed_row_count: must match the sum of summarized input rows")

    _check_artifact_handling(payload, errors)

    receipt = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "error_count": int(len(errors)),
        "warnings": sorted(set(warnings)),
        "errors": sorted(set(errors)),
    }
    return errors, warnings, receipt


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(args.input_json)
        errors, warnings, receipt = _validate(payload)
    except Exception as exc:  # noqa: BLE001
        errors = [str(exc)]
        warnings = []
        receipt = {
            "script_name": SCRIPT_NAME,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "ok": False,
            "error_count": 1,
            "warnings": [],
            "errors": errors,
        }

    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")

    print(_json_text(receipt, args.pretty))
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
