#!/usr/bin/env python3
"""Audit progression/adversary receipts for sparse-coverage/operator artifacts.

The script reads one or more JSON or CSV inputs, classifies rows with a small
set of conservative artifact heuristics, and emits candidate-only JSON.
It does not perform numeric solves or promotion checks.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import re
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_kn_progression_artifact_audit.py"
SCHEMA_VERSION = "1.0.0"

NEAR_ZERO_LAMBDA_EPS = 1.0e-8
LOW_D_MAX = 3.0

ROW_CONTAINER_KEYS = (
    "rows",
    "row",
    "records",
    "record",
    "entries",
    "entry",
    "items",
    "item",
    "candidates",
    "candidate_rows",
    "receipts",
    "receipt_rows",
    "artifacts",
    "artifact_rows",
    "summaries",
    "summary_rows",
    "canonical_rows",
    "canonical_rows_excluding_artifacts",
    "data",
    "payload",
)

ARTIFACT_KEY_HINTS = {
    "artifact",
    "artifacts",
    "isartifact",
    "artifactflag",
    "rowartifact",
    "markedartifact",
    "artifactrow",
}

LAMBDA_KEY_HINTS = (
    "lambda",
    "rayleigh",
    "eigval",
    "eigenvalue",
    "lowesteigenvalue",
    "minlambda",
    "lambda_min",
)

D_KEY_HINTS = (
    "d",
    "d0",
    "lowd",
    "lowdimension",
    "degree",
    "dimension",
)

SHELL_KEY_HINTS = (
    "shell",
    "eigenshell",
    "mode",
    "radialshell",
    "worstshell",
    "topshell",
    "shellmax",
    "highestshell",
)

COVERAGE_KEY_HINTS = (
    "coverage",
    "coveragefraction",
    "coveragepct",
    "coveragepercent",
    "supportcoverage",
    "operatorcoverage",
    "shellcoverage",
)

COND_KEY_HINTS = (
    "conditionnumber",
    "conditionnum",
    "condnumber",
    "condnum",
    "conditioning",
    "cond",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        action="append",
        type=Path,
        required=True,
        help="JSON or CSV receipt/summaries to audit; repeatable.",
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _normalize_key(key: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", key.lower())


def _normalize_scalar(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float)):
        if isinstance(value, float) and not math.isfinite(value):
            return None
        return value
    if isinstance(value, str):
        stripped = value.strip()
        if stripped == "":
            return ""
        if stripped.lower() in {"true", "false"}:
            return stripped.lower() == "true"
        if re.fullmatch(r"[-+]?\d+", stripped):
            try:
                return int(stripped)
            except ValueError:
                return stripped
        try:
            if stripped.endswith("%"):
                parsed = float(stripped[:-1])
                return parsed / 100.0 if math.isfinite(parsed) else stripped
            parsed = float(stripped)
        except ValueError:
            return stripped
        return parsed if math.isfinite(parsed) else stripped
    return value


def _normalize_value(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(key): _normalize_value(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_normalize_value(item) for item in value]
    return _normalize_scalar(value)


def _coerce_csv_rows(path: Path) -> list[dict[str, Any]]:
    with path.open(newline="", encoding="utf-8-sig") as handle:
        reader = csv.DictReader(handle)
        rows: list[dict[str, Any]] = []
        for row in reader:
            rows.append({str(key): _normalize_scalar(value) for key, value in row.items()})
        return rows


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _rows_from_json_payload(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, list):
        return [item for item in payload if isinstance(item, dict)]
    if not isinstance(payload, dict):
        return []

    for key in ROW_CONTAINER_KEYS:
        value = payload.get(key)
        if isinstance(value, list):
            rows = [item for item in value if isinstance(item, dict)]
            if rows:
                return rows

    # Fall back to treating a row-shaped object as a single receipt row.
    row_hints = set()
    for key in payload:
        normalized = _normalize_key(str(key))
        if (
            any(hint in normalized for hint in LAMBDA_KEY_HINTS)
            or any(hint in normalized for hint in D_KEY_HINTS)
            or any(hint in normalized for hint in SHELL_KEY_HINTS)
            or any(hint in normalized for hint in COVERAGE_KEY_HINTS)
            or any(hint in normalized for hint in COND_KEY_HINTS)
            or normalized in {"artifact", "isartifact", "rowartifact", "markedartifact"}
        ):
            row_hints.add(normalized)
    return [payload] if row_hints else []


def _load_rows(path: Path) -> tuple[list[dict[str, Any]], str]:
    suffix = path.suffix.lower()
    if suffix == ".csv":
        return _coerce_csv_rows(path), "csv"
    if suffix == ".json":
        payload = _load_json(path)
        return _rows_from_json_payload(payload), "json"
    raise ValueError(f"unsupported input type: {path}")


def _scalar_number(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        parsed = float(value)
        return parsed if math.isfinite(parsed) else None
    if isinstance(value, str):
        stripped = value.strip()
        if stripped == "":
            return None
        try:
            parsed = float(stripped)
        except ValueError:
            return None
        return parsed if math.isfinite(parsed) else None
    return None


def _truthy(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return math.isfinite(float(value)) and float(value) != 0.0
    if isinstance(value, str):
        normalized = value.strip().lower()
        return normalized in {"1", "true", "yes", "y", "artifact", "artifactual"}
    return False


def _falsey(value: Any) -> bool:
    if value is None:
        return True
    if isinstance(value, bool):
        return not value
    if isinstance(value, (int, float)):
        return math.isfinite(float(value)) and float(value) == 0.0
    if isinstance(value, str):
        normalized = value.strip().lower()
        return normalized in {"", "0", "0.0", "false", "none", "null", "no", "n"}
    return False


def _matching_keys(row: dict[str, Any], hints: tuple[str, ...]) -> list[str]:
    matches: list[str] = []
    for key in row:
        normalized = _normalize_key(str(key))
        if any(hint in normalized for hint in hints):
            matches.append(str(key))
    return matches


def _artifact_reasons(row: dict[str, Any]) -> list[str]:
    reasons: list[str] = []
    for key in row:
        normalized = _normalize_key(str(key))
        value = row.get(key)
        if normalized in ARTIFACT_KEY_HINTS and _truthy(value):
            reasons.append(f"{key}=artifact")
        elif normalized == "status" and isinstance(value, str) and "artifact" in value.lower():
            reasons.append("status=artifact")
        elif "artifact" in normalized and not _falsey(value):
            reasons.append(f"{key}=artifact")
    return sorted(set(reasons))


def _coverage_reasons(row: dict[str, Any]) -> list[str]:
    reasons: list[str] = []
    coverage_keys = _matching_keys(row, COVERAGE_KEY_HINTS)
    if coverage_keys:
        for key in coverage_keys:
            value = row.get(key)
            if _falsey(value):
                reasons.append(f"{key}=missing_or_zero")
            else:
                numeric = _scalar_number(value)
                if numeric is not None and numeric <= 0.0:
                    reasons.append(f"{key}=zero")
    return sorted(set(reasons))


def _condition_number_reasons(row: dict[str, Any]) -> list[str]:
    reasons: list[str] = []
    cond_keys = _matching_keys(row, COND_KEY_HINTS)
    for key in cond_keys:
        value = row.get(key)
        if isinstance(value, (dict, list)):
            continue
        if value is None or (isinstance(value, str) and value.strip() == ""):
            continue
        reasons.append(f"{key}=present")
    return sorted(set(reasons))


def _lambda_field(row: dict[str, Any]) -> tuple[str | None, float | None]:
    for key in row:
        normalized = _normalize_key(str(key))
        if any(hint in normalized for hint in LAMBDA_KEY_HINTS):
            numeric = _scalar_number(row.get(key))
            if numeric is not None:
                return str(key), numeric
    return None, None


def _d_field(row: dict[str, Any]) -> tuple[str | None, float | None]:
    for key in row:
        normalized = _normalize_key(str(key))
        if normalized == "d" or any(hint in normalized for hint in D_KEY_HINTS if hint != "d"):
            numeric = _scalar_number(row.get(key))
            if numeric is not None:
                return str(key), numeric
    return None, None


def _top_shell_evidence(row: dict[str, Any]) -> list[str]:
    evidence: list[str] = []
    for key, value in row.items():
        normalized = _normalize_key(str(key))
        if not any(hint in normalized for hint in SHELL_KEY_HINTS):
            if isinstance(value, str):
                lowered = value.lower()
                if any(token in lowered for token in ("top-shell", "top shell", "worst shell", "shell max", "highest shell")):
                    evidence.append(str(key))
            continue

        if any(token in normalized for token in ("topshell", "shellmax", "worstshell", "highestshell")):
            evidence.append(str(key))
            continue

        if isinstance(value, str):
            lowered = value.lower()
            if any(token in lowered for token in ("top-shell", "top shell", "worst shell", "shell max", "highest shell")):
                evidence.append(str(key))
                continue

        if isinstance(value, bool) and value:
            evidence.append(str(key))
            continue

        if isinstance(value, (int, float)) and "max" in normalized:
            evidence.append(str(key))

    return sorted(set(evidence))


def _near_zero_lambda_low_d_top_shell(row: dict[str, Any]) -> list[str]:
    reasons: list[str] = []
    lambda_key, lambda_value = _lambda_field(row)
    if lambda_value is None or abs(float(lambda_value)) > NEAR_ZERO_LAMBDA_EPS:
        return reasons

    d_key, d_value = _d_field(row)
    if d_value is None or float(d_value) > LOW_D_MAX:
        return reasons

    top_shell = _top_shell_evidence(row)
    if not top_shell:
        return reasons

    reasons.append(
        f"{lambda_key or 'lambda'}~0 with {d_key or 'D'}={d_value:g} and top-shell evidence"
    )
    return reasons


def _suspect_reasons(row: dict[str, Any]) -> list[str]:
    reasons = []
    coverage_reasons = _coverage_reasons(row)
    condition_reasons = _condition_number_reasons(row)
    reasons.extend(_artifact_reasons(row))
    reasons.extend(_near_zero_lambda_low_d_top_shell(row))
    reasons.extend(coverage_reasons)
    reasons.extend(condition_reasons)

    return sorted(set(reasons))


def _canonical_fingerprint(row: dict[str, Any]) -> str:
    return json.dumps(row, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _merge_sources(existing: dict[str, Any], incoming_source: str) -> None:
    sources = existing.setdefault("source_inputs", [])
    if incoming_source not in sources:
        sources.append(incoming_source)


def _row_record(row: dict[str, Any], *, source_input: str, source_format: str, row_index: int) -> dict[str, Any]:
    canonical_row = _normalize_value(row)
    if not isinstance(canonical_row, dict):
        canonical_row = {"value": canonical_row}
    artifact_reasons = _artifact_reasons(canonical_row)
    suspect_reasons = _suspect_reasons(canonical_row)
    return {
        **canonical_row,
        "_audit": {
            "source_inputs": [source_input],
            "source_format": source_format,
            "source_row_index": row_index,
            "artifact": bool(artifact_reasons),
            "suspect": bool(suspect_reasons),
            "reasons": suspect_reasons,
        },
    }


def main() -> int:
    args = _parse_args()

    ordered_rows: list[dict[str, Any]] = []
    merged: dict[str, dict[str, Any]] = {}
    artifact_count = 0
    suspect_count = 0

    for input_path in args.input:
        rows, source_format = _load_rows(input_path)
        for row_index, row in enumerate(rows):
            record = _row_record(row, source_input=input_path.as_posix(), source_format=source_format, row_index=row_index)
            audit = record["_audit"]
            fingerprint = _canonical_fingerprint({key: value for key, value in record.items() if key != "_audit"})

            if fingerprint not in merged:
                merged[fingerprint] = record
                ordered_rows.append(record)
            else:
                existing = merged[fingerprint]
                _merge_sources(existing["_audit"], input_path.as_posix())
                existing["_audit"]["artifact"] = bool(existing["_audit"]["artifact"] or audit["artifact"])
                existing["_audit"]["suspect"] = bool(existing["_audit"]["suspect"] or audit["suspect"])
                existing["_audit"]["reasons"] = sorted(
                    set(existing["_audit"]["reasons"]) | set(audit["reasons"])
                )

    canonical_rows: list[dict[str, Any]] = []
    for record in ordered_rows:
        audit = record["_audit"]
        if audit["artifact"]:
            artifact_count += 1
        if audit["suspect"]:
            suspect_count += 1
        if not audit["artifact"]:
            canonical_rows.append(record)

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": "ns_triad_kn_progression_artifact_audit",
        "route_decision": "FAIL_CLOSED_NS_TRIAD_KN_PROGRESSION_ARTIFACT_AUDIT",
        "schema_version": SCHEMA_VERSION,
        "status": "ok",
        "ok": True,
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "input_count": len(args.input),
        "row_count": len(ordered_rows),
        "artifact_count": artifact_count,
        "suspect_count": suspect_count,
        "canonical_rows_excluding_artifacts": canonical_rows,
    }
    text = _json_text(payload, args.pretty)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
