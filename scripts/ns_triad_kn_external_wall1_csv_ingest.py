#!/usr/bin/env python3
"""Ingest the external Wall1 CSVs and emit a compact canonical summary."""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import Counter
from pathlib import Path
from typing import Any, Iterable


SCRIPT_NAME = "scripts/ns_triad_kn_external_wall1_csv_ingest.py"
CONTRACT = "ns_triad_kn_external_wall1_csv_ingest"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EXTERNAL_WALL1_CSV_INGEST"
SCHEMA_VERSION = "1.0.0"
DEFAULT_CSVS = (
    Path("/home/c/Downloads/wall1_progression_N3_N6.csv"),
    Path("/home/c/Downloads/wall1_N3_eigenmode_escape.csv"),
    Path("/home/c/Downloads/wall1_eigenmode_audit_N2.csv"),
    Path("/home/c/Downloads/wall1_constrained_adversarial.csv"),
    Path("/home/c/Downloads/wall1_squarewave_fork.csv"),
)

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
COUNT_STYLE_KEYS = ("danger", "artifact", "branch")

TRUE_STRINGS = {"true", "t", "yes", "y", "1"}
FALSE_STRINGS = {"false", "f", "no", "n", "0"}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--csv",
        action="append",
        type=Path,
        default=None,
        help="Input CSV path; may be repeated. If omitted, the five Wall1 defaults are used when present.",
    )
    parser.add_argument("--output-json", type=Path, required=True, help="Path to write the summary JSON.")
    return parser.parse_args()


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        parsed = float(value)
    else:
        text = str(value).strip()
        if not text:
            return None
        try:
            parsed = float(text)
        except ValueError:
            return None
    if not math.isfinite(parsed):
        return None
    return parsed


def _coerce_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if value is None:
        return None
    text = str(value).strip().lower()
    if not text:
        return None
    if text in TRUE_STRINGS:
        return True
    if text in FALSE_STRINGS:
        return False
    return None


def _load_csv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    with path.open("r", newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise ValueError(f"missing header row: {path}")
        rows = list(reader)
        return list(reader.fieldnames), rows


def _mean(values: Iterable[float]) -> float | None:
    values_list = list(values)
    if not values_list:
        return None
    return sum(values_list) / len(values_list)


def _numeric_stats(rows: list[dict[str, str]], columns: list[str]) -> dict[str, dict[str, float | int]]:
    stats: dict[str, dict[str, float | int]] = {}
    for column in columns:
        values: list[float] = []
        for row in rows:
            parsed = _coerce_float(row.get(column))
            if parsed is not None:
                values.append(parsed)
        if values:
            stats[column] = {
                "count": len(values),
                "min": min(values),
                "max": max(values),
                "mean": _mean(values),
            }
    return stats


def _categorical_counts(rows: list[dict[str, str]], column: str) -> dict[str, Any] | None:
    values = [row.get(column) for row in rows if row.get(column) not in (None, "")]
    if not values:
        return None
    bool_values = [_coerce_bool(value) for value in values]
    if all(value is not None for value in bool_values):
        true_count = sum(1 for value in bool_values if value is True)
        false_count = sum(1 for value in bool_values if value is False)
        return {
            "kind": "boolean",
            "true_count": true_count,
            "false_count": false_count,
            "other_count": len(values) - true_count - false_count,
        }
    if column == "branch":
        counts = Counter(str(value).strip() for value in values if str(value).strip())
        return {
            "kind": "categorical",
            "value_counts": dict(sorted(counts.items())),
            "distinct_count": len(counts),
        }
    return None


def _value_preview(values: Iterable[Any]) -> list[Any]:
    unique: list[Any] = []
    seen: set[str] = set()
    for value in values:
        key = json.dumps(value, sort_keys=True, default=str)
        if key in seen:
            continue
        seen.add(key)
        unique.append(value)
    return unique


def _file_summary(path: Path, columns: list[str], rows: list[dict[str, str]]) -> dict[str, Any]:
    numeric_stats = _numeric_stats(rows, columns)
    counts: dict[str, Any] = {}
    for key in COUNT_STYLE_KEYS:
        if key in columns:
            counts[key] = _categorical_counts(rows, key)
    artifact_true = 0
    artifact_false = 0
    artifact_other = 0
    if "artifact" in columns:
        for row in rows:
            parsed = _coerce_bool(row.get("artifact"))
            if parsed is True:
                artifact_true += 1
            elif parsed is False:
                artifact_false += 1
            elif row.get("artifact") not in (None, ""):
                artifact_other += 1
    branch_values = [row.get("branch") for row in rows if row.get("branch") not in (None, "")]
    danger_values = [row.get("danger") for row in rows if row.get("danger") not in (None, "")]
    focus_measures = {}
    for key in ("lambda_min", "lmin", "D", "worst_e_shell", "worst_eigen_shell"):
        if key in numeric_stats:
            focus_measures[key] = numeric_stats[key]
    return {
        "path": str(path),
        "filename": path.name,
        "row_count": len(rows),
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_promoted": False,
        "clay_promoted": False,
        "columns": columns,
        "numeric_stats": numeric_stats,
        "focus_numeric_stats": focus_measures,
        "counts": {
            **{key: value for key, value in counts.items() if value is not None},
            **(
                {
                    "artifact_true_count": artifact_true,
                    "artifact_false_count": artifact_false,
                    "artifact_other_count": artifact_other,
                }
                if "artifact" in columns
                else {}
            ),
            **(
                {
                    "branch_values": _value_preview(branch_values),
                    "branch_value_count": len(branch_values),
                }
                if branch_values
                else {}
            ),
            **(
                {
                    "danger_true_count": sum(1 for value in danger_values if _coerce_bool(value) is True),
                    "danger_false_count": sum(1 for value in danger_values if _coerce_bool(value) is False),
                    "danger_other_count": sum(
                        1 for value in danger_values if value not in (None, "") and _coerce_bool(value) is None
                    ),
                }
                if danger_values
                else {}
            ),
        },
    }


def _canonical_summary(
    file_summaries: list[dict[str, Any]],
    file_rows: list[tuple[str, list[dict[str, str]]]],
) -> dict[str, Any]:
    all_rows: list[dict[str, Any]] = []
    for filename, rows in file_rows:
        for row in rows:
            all_rows.append({"source_file": filename, **row})

    lmin_candidates: list[dict[str, Any]] = []
    d_values: list[float] = []
    worst_e_shell_values: list[float] = []
    worst_eigen_shell_values: list[float] = []
    artifact_true = 0
    artifact_false = 0
    artifact_other = 0
    danger_true = 0
    danger_false = 0
    danger_other = 0

    for row in all_rows:
        for column in ("lambda_min", "lmin"):
            value = _coerce_float(row.get(column))
            if value is not None:
                lmin_candidates.append({"source_file": row["source_file"], "column": column, "value": value})
        d_value = _coerce_float(row.get("D"))
        if d_value is not None:
            d_values.append(d_value)
        worst_e_shell_value = _coerce_float(row.get("worst_e_shell"))
        if worst_e_shell_value is not None:
            worst_e_shell_values.append(worst_e_shell_value)
        worst_eigen_shell_value = _coerce_float(row.get("worst_eigen_shell"))
        if worst_eigen_shell_value is not None:
            worst_eigen_shell_values.append(worst_eigen_shell_value)
        artifact_value = _coerce_bool(row.get("artifact"))
        if artifact_value is True:
            artifact_true += 1
        elif artifact_value is False:
            artifact_false += 1
        elif row.get("artifact") not in (None, ""):
            artifact_other += 1
        danger_value = _coerce_bool(row.get("danger"))
        if danger_value is True:
            danger_true += 1
        elif danger_value is False:
            danger_false += 1
        elif row.get("danger") not in (None, ""):
            danger_other += 1

    def _stats(values: list[float]) -> dict[str, float | int] | None:
        if not values:
            return None
        return {
            "count": len(values),
            "min": min(values),
            "max": max(values),
            "mean": _mean(values),
        }

    lmin_min = min(lmin_candidates, key=lambda item: item["value"]) if lmin_candidates else None
    lmin_max = max(lmin_candidates, key=lambda item: item["value"]) if lmin_candidates else None

    return {
        "row_count": len(all_rows),
        "file_count": len(file_summaries),
        "file_summary_count": len(file_summaries),
        "summarized_file_count": len(file_summaries),
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_promoted": False,
        "clay_promoted": False,
        "files": [summary["filename"] for summary in file_summaries],
        "lambda_min_lmin": {
            "min": lmin_min,
            "max": lmin_max,
            "stats": _stats([item["value"] for item in lmin_candidates]),
        },
        "D": _stats(d_values),
        "worst_e_shell": _stats(worst_e_shell_values),
        "worst_eigen_shell": _stats(worst_eigen_shell_values),
        "artifact": {
            "true_count": artifact_true,
            "false_count": artifact_false,
            "other_count": artifact_other,
            "present": artifact_true + artifact_false + artifact_other > 0,
        },
        "danger": {
            "true_count": danger_true,
            "false_count": danger_false,
            "other_count": danger_other,
            "present": danger_true + danger_false + danger_other > 0,
        },
        "source_files_with_focus_columns": sorted(
            {
                summary["filename"]
                for summary in file_summaries
                if any(key in summary.get("columns", []) for key in ("lmin", "lambda_min", "D", "worst_e_shell", "worst_eigen_shell", "artifact", "danger"))
            }
        ),
    }


def _control_card() -> dict[str, str]:
    return {
        "O": "Ingest the five external Wall1 CSVs and summarize their numeric and danger-style structure.",
        "R": "Produce per-file row counts, column inventories, numeric stats, and a canonical Wall1 summary.",
        "C": SCRIPT_NAME,
        "S": "Deterministic CSV parse and summarization only; no theorem or Clay promotion is inferred.",
        "L": "Read repeated --csv inputs or the five default Wall1 CSVs, then write JSON to --output-json.",
        "P": "FAIL_CLOSED_WALL1_EXTERNAL_CSV_INGEST",
        "G": "Candidate-only telemetry: theorem_promoted and clay_promoted stay false.",
        "F": "Focus on lambda_min/lmin, D, worst_e_shell, worst_eigen_shell, artifact, and danger fields.",
    }


def main() -> int:
    args = _parse_args()
    csv_paths = list(args.csv) if args.csv else [path for path in DEFAULT_CSVS if path.exists()]
    if not csv_paths:
        raise FileNotFoundError("no input CSVs were provided and none of the default Wall1 CSVs exist")

    file_summaries: list[dict[str, Any]] = []
    file_rows: list[tuple[str, list[dict[str, str]]]] = []
    for path in csv_paths:
        columns, rows = _load_csv(path)
        file_summaries.append(_file_summary(path, columns, rows))
        file_rows.append((path.name, rows))
    payload = {
        **_control_card(),
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "status": "ok",
        "ok": True,
        "error_count": 0,
        "warnings": [],
        "empirical_non_promoting": True,
        "theorem_promoted": False,
        "clay_promoted": False,
        "candidate_only": True,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "theorem_promoted": False,
            "clay_promoted": False,
        },
        "inputs": [str(path) for path in csv_paths],
        "file_summaries": file_summaries,
        "canonical_summary": _canonical_summary(file_summaries, file_rows),
    }
    payload["row_count"] = int(payload["canonical_summary"]["row_count"])
    payload["total_row_count"] = int(payload["canonical_summary"]["row_count"])
    artifact_summary = payload["canonical_summary"]["artifact"]
    if artifact_summary["present"]:
        payload["artifact_handling"] = {
            "present": True,
            "handled": True,
            "recorded": True,
            "path": ", ".join(
                str(path) for path in csv_paths if "N3_N6" in path.name or "progression" in path.name
            ),
            "policy": "artifact rows are recorded and excluded by downstream artifact audit before canonical progression claims",
        }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
