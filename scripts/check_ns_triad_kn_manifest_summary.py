#!/usr/bin/env python3
"""Summarize parallel mixed-tail manifest receipts into theorem-facing branches."""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, PARTIAL_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/check_ns_triad_kn_manifest_summary.py"
CONTRACT = "check_ns_triad_kn_manifest_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_MANIFEST_SUMMARY"
SCHEMA_VERSION = "1.0.0"
DEFAULT_C0 = 0.25


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-json", type=Path, default=None)
    parser.add_argument("--run-summary-json", type=Path, default=None)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-md", type=Path, required=True)
    parser.add_argument("--c0", type=float, default=DEFAULT_C0)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _component_for_cutoff(result: dict[str, Any], cutoff: int) -> dict[str, Any]:
    for row in result.get("component_rayleigh_splits", []):
        if isinstance(row, dict) and int(row.get("tail_cutoff", -1)) == int(cutoff):
            return row
    return {}


def _tail_worst_shell(result: dict[str, Any], cutoff: int) -> int | None:
    candidates = [
        row
        for row in result.get("eigen_mass_by_shell", [])
        if isinstance(row, dict)
        and int(row.get("shell", -1)) >= int(cutoff)
        and _finite_float(row.get("eigen_mass")) is not None
    ]
    if not candidates:
        return None
    return int(max(candidates, key=lambda row: float(row.get("eigen_mass", 0.0)))["shell"])


def _job_rows_from_manifest(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    return [job for job in manifest.get("jobs", []) if isinstance(job, dict)]


def _job_rows_from_run_summary(summary: dict[str, Any]) -> list[dict[str, Any]]:
    return [run for run in summary.get("runs", []) if isinstance(run, dict)]


def _receipt_path(row: dict[str, Any]) -> Path | None:
    path_text = row.get("output_json")
    if not isinstance(path_text, str) or not path_text:
        return None
    return Path(path_text)


def _d0_thresholds(row: dict[str, Any], receipt: dict[str, Any] | None) -> list[float]:
    values = row.get("d0_thresholds", row.get("D0"))
    if isinstance(values, list):
        return [float(value) for value in values]
    if values is not None:
        return [float(values)]
    if receipt:
        result = receipt.get("result", {})
        flags = result.get("D0_flags", {}) if isinstance(result, dict) else {}
        if isinstance(flags, dict):
            parsed = []
            for key in flags:
                try:
                    parsed.append(float(key))
                except ValueError:
                    pass
            return sorted(parsed)
    return []


def _classify(*, r_full: float | None, r_tail: float | None, d_value: float | None, c0: float) -> str:
    if r_full is None:
        return "no_receipt"
    if r_full >= c0:
        return "no_low_frame"
    if r_tail is None:
        return "low_frame_no_tail_quotient"
    if r_tail >= c0:
        return "finite_anchor_mixed_low_frame"
    if d_value is None:
        return "tail_internal_low_frame_unknown_D"
    return "tail_internal_low_frame"


def _classify_by_d0(branch: str, d_value: float | None, thresholds: list[float]) -> dict[str, str]:
    result: dict[str, str] = {}
    for threshold in thresholds:
        key = f"{threshold:g}"
        if branch != "tail_internal_low_frame":
            result[key] = branch
        elif d_value is None:
            result[key] = "tail_internal_low_frame_unknown_D"
        elif float(d_value) > float(threshold):
            result[key] = "high_D_tail_internal_low_frame"
        else:
            result[key] = "low_D_tail_internal_obstruction"
    return result


def _summarize_receipt(row: dict[str, Any], receipt: dict[str, Any], c0: float) -> dict[str, Any]:
    result = receipt.get("result", {})
    if not isinstance(result, dict):
        result = {}
    cutoff = int(result.get("tail_responsibility_summary", {}).get("tail_cutoff", row.get("K", row.get("tail_cutoff", 0))))
    split = _component_for_cutoff(result, cutoff)
    metrics = result.get("profile_metrics", {})
    tail_summary = result.get("tail_responsibility_summary", {})
    d_value = _finite_float(metrics.get("dissipation_proxy") if isinstance(metrics, dict) else None)
    r_full = _finite_float(split.get("full_rayleigh_from_terms"))
    r_tail = _finite_float(split.get("tail_only_rayleigh"))
    branch = _classify(r_full=r_full, r_tail=r_tail, d_value=d_value, c0=float(c0))
    thresholds = _d0_thresholds(row, receipt)
    return {
        "job_id": row.get("job_id"),
        "status": receipt.get("status"),
        "branch": branch,
        "branch_by_D0": _classify_by_d0(branch, d_value, thresholds),
        "backend": row.get("backend", result.get("backend")),
        "shell": int(result.get("shell", row.get("shell", 0))),
        "K": cutoff,
        "eta": float(result.get("tail_eta", row.get("eta", row.get("tail_eta", 0.0)))),
        "profile_family": row.get("profile_family", "forced-tail"),
        "lambda_min": _finite_float(result.get("lambda_min")),
        "R_full": r_full,
        "R_finite": _finite_float(split.get("finite_only_rayleigh")),
        "R_tail": r_tail,
        "R_cross": _finite_float(split.get("cross_term_rayleigh")),
        "tail_mass": _finite_float(split.get("tail_euclidean_mass")),
        "finite_mass": _finite_float(split.get("finite_euclidean_mass")),
        "worst_shell": tail_summary.get("worst_eigen_shell") if isinstance(tail_summary, dict) else None,
        "tail_only_worst_shell": _tail_worst_shell(result, cutoff),
        "profile_tail_mass": tail_summary.get("profile_tail_mass") if isinstance(tail_summary, dict) else None,
        "D": d_value,
        "detail_json": str(_receipt_path(row) or ""),
        "warnings": receipt.get("warnings", []) + row.get("warnings", []),
    }


def _summarize_missing(row: dict[str, Any], reason: str) -> dict[str, Any]:
    branch = reason
    if reason == "empty_tail_subspace":
        branch = "empty_tail_subspace"
    return {
        "job_id": row.get("job_id"),
        "status": "skipped" if reason == "empty_tail_subspace" else "missing",
        "branch": branch,
        "branch_by_D0": {},
        "backend": row.get("backend"),
        "shell": row.get("shell"),
        "K": row.get("K", row.get("tail_cutoff")),
        "eta": row.get("eta", row.get("tail_eta")),
        "profile_family": row.get("profile_family"),
        "lambda_min": None,
        "R_full": None,
        "R_finite": None,
        "R_tail": None,
        "R_cross": None,
        "tail_mass": None,
        "finite_mass": None,
        "worst_shell": None,
        "tail_only_worst_shell": None,
        "profile_tail_mass": None,
        "D": None,
        "detail_json": str(_receipt_path(row) or ""),
        "warnings": row.get("warnings", []),
    }


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N Manifest Summary",
        "",
        f"- status: `{payload['status']}`",
        f"- c0: `{fmt(payload['c0'])}`",
        f"- rows: `{payload['row_count']}`",
        f"- missing/failed rows: `{payload['missing_or_failed_count']}`",
        "",
        "## Branch Counts",
        "",
    ]
    for key, value in sorted(payload["branch_counts"].items()):
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| backend | N | K | eta | branch | lambda | R_full | R_finite | R_tail | D | worst shell | tail worst |",
            "|---|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["rows"]:
        lines.append(
            f"| {row['backend']} | {row['shell']} | {row['K']} | {fmt(row['eta'])} | {row['branch']} | "
            f"{fmt(row['lambda_min'])} | {fmt(row['R_full'])} | {fmt(row['R_finite'])} | "
            f"{fmt(row['R_tail'])} | {fmt(row['D'])} | {fmt(row['worst_shell'])} | {fmt(row['tail_only_worst_shell'])} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    source: dict[str, Any]
    if args.run_summary_json is not None:
        source = _load_json(args.run_summary_json)
        rows = _job_rows_from_run_summary(source)
        source_json = str(args.run_summary_json)
    elif args.manifest_json is not None:
        source = _load_json(args.manifest_json)
        rows = _job_rows_from_manifest(source)
        source_json = str(args.manifest_json)
    else:
        raise SystemExit("provide --manifest-json or --run-summary-json")

    summaries: list[dict[str, Any]] = []
    for row in rows:
        if row.get("skip_reason") == "empty_tail_subspace" or row.get("status") == "empty_tail_subspace":
            summaries.append(_summarize_missing(row, "empty_tail_subspace"))
            continue
        path = _receipt_path(row)
        if path is None or not path.exists():
            summaries.append(_summarize_missing(row, "missing_receipt"))
            continue
        try:
            receipt = _load_json(path)
        except (OSError, json.JSONDecodeError, ValueError):
            summaries.append(_summarize_missing(row, "bad_receipt"))
            continue
        if receipt.get("status") != OK_STATUS:
            summaries.append(_summarize_missing(row, "failed_receipt"))
            continue
        summaries.append(_summarize_receipt(row, receipt, float(args.c0)))

    summaries.sort(key=lambda row: (str(row.get("backend")), int(row.get("shell") or 0), int(row.get("K") or 0), float(row.get("eta") or 0.0)))
    branch_counts = Counter(str(row.get("branch")) for row in summaries)
    d0_counts: dict[str, dict[str, int]] = {}
    for row in summaries:
        for threshold, branch in row.get("branch_by_D0", {}).items():
            d0_counts.setdefault(str(threshold), {})
            d0_counts[str(threshold)][str(branch)] = d0_counts[str(threshold)].get(str(branch), 0) + 1

    missing_or_failed_count = sum(1 for row in summaries if row.get("status") not in {OK_STATUS, "skipped"})
    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": OK_STATUS if missing_or_failed_count == 0 else PARTIAL_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "source_json": source_json,
        "c0": float(args.c0),
        "row_count": len(summaries),
        "missing_or_failed_count": missing_or_failed_count,
        "branch_counts": dict(branch_counts),
        "branch_counts_by_D0": d0_counts,
        "rows": summaries,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    args.output_md.parent.mkdir(parents=True, exist_ok=True)
    args.output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0 if missing_or_failed_count == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
