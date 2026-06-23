#!/usr/bin/env python3
"""Summarize NS triad K_N(A) batch manifests into a compact candidate receipt."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_NAME = "scripts/ns_triad_kn_batch_manifest_summary.py"
CONTRACT = "ns_triad_kn_batch_manifest_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_BATCH_MANIFEST_SUMMARY"
SCHEMA_VERSION = "1.0.0"

AUTHORITY = {
    "candidate_only": True,
    "gpu_kn_authority": False,
    "clay_authority": False,
    "clay_promoted": False,
    "theorem_promoted": False,
    "full_ns_promoted": False,
    "promoted": False,
}

BEST_LAMBDA_KEYS = (
    "lambda_min_iterative",
    "lambda_min_dense_cpu",
    "lambda_rank",
    "best_lambda",
    "lambda_min",
)
WORST_SHELL_KEYS = (
    "worst_eigenvector_shell_iterative",
    "worst_eigenvector_shell_dense_cpu",
    "worst_eigenvector_shell",
    "eigen_shell_max_with_mass_eta",
)
WORST_MASS_KEYS = (
    "worst_eigenvector_shell_mass_iterative",
    "worst_eigenvector_shell_mass_dense_cpu",
    "worst_eigenvector_shell_mass",
)
TAIL_ESCAPE_KEYS = (
    "tail_escape_candidate_count",
    "tail_escape_count",
    "eigenvector_tail_escape_count",
)
TRIAD_COVERAGE_KEYS = (
    "triad_coverage_status",
    "coverage_status",
    "triad_coverage",
    "coverage",
)
SPARSE_SAMPLE_COVERAGE_STATUSES = {
    "sparse",
    "sparse_sampled",
    "limited",
    "partial",
}
FULL_SAMPLE_COVERAGE_STATUSES = {
    "full",
    "fully_covered",
    "covered",
    "complete",
    "operator_full",
    "sample_full",
}
ZERO_DEGREE_COUNT_KEYS = (
    "operator_zero_degree_mode_count",
    "zero_degree_count",
    "degree_zero_count",
    "zero_degree_counter",
    "degree_zero_counter",
)
EMPTY_DEGREE_COUNT_KEYS = (
    "operator_empty_triad_count",
    "empty_degree_count",
    "degree_empty_count",
    "empty_degree_counter",
    "degree_empty_counter",
)


def _json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be an object")
    return payload


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value)
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return None
    return parsed


def _first_float(mapping: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        value = _coerce_float(mapping.get(key))
        if value is not None:
            return value
    return None


def _first_int(mapping: dict[str, Any], keys: tuple[str, ...]) -> int | None:
    for key in keys:
        value = _coerce_int(mapping.get(key))
        if value is not None:
            return value
    return None


def _resolve_path(path_text: str, base_dir: Path) -> Path:
    path = Path(path_text)
    if path.is_absolute():
        return path
    candidate = (base_dir / path).resolve()
    if candidate.exists():
        return candidate
    repo_candidate = (REPO_ROOT / path).resolve()
    if repo_candidate.exists():
        return repo_candidate
    return candidate


def _load_json_maybe(path_text: str | None, base_dir: Path) -> dict[str, Any] | None:
    if not isinstance(path_text, str) or not path_text.strip():
        return None
    path = _resolve_path(path_text, base_dir)
    if not path.exists():
        return None
    try:
        return _read_json(path)
    except (OSError, json.JSONDecodeError, ValueError):
        return None


def _manifest_runs(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    runs = manifest.get("runs")
    if isinstance(runs, list):
        return [run for run in runs if isinstance(run, dict)]
    return []


def _scan_payload(run: dict[str, Any], manifest_dir: Path) -> dict[str, Any] | None:
    scan = run.get("scan")
    if isinstance(scan, dict):
        for key in ("receipt_path", "source_json", "json_path", "output_json"):
            payload = _load_json_maybe(scan.get(key), manifest_dir)
            if payload is not None:
                return payload
    if "rows" in run or "aggregate" in run or "summary" in run:
        return run
    return None


def _select_row(payload: dict[str, Any], shell: int | None) -> dict[str, Any] | None:
    rows = payload.get("rows")
    if isinstance(rows, list):
        candidates = [row for row in rows if isinstance(row, dict)]
        if shell is not None:
            for row in candidates:
                row_shell = _coerce_int(row.get("shell"))
                if row_shell == shell:
                    return row
                if row_shell is None and _coerce_int(row.get("snapshot_index")) == shell:
                    return row
        if candidates:
            return candidates[0]
    return payload


def _candidate_profiles(container: dict[str, Any]) -> list[dict[str, Any]]:
    profiles: list[dict[str, Any]] = []
    for key in ("best_low_lambda_profile", "best_profile", "best_global_profile"):
        value = container.get(key)
        if isinstance(value, dict):
            profiles.append(value)
    for key in ("candidate_receipts", "best_low_lambda_rows", "profile_samples"):
        value = container.get(key)
        if isinstance(value, list):
            profiles.extend(item for item in value if isinstance(item, dict))
    profiles.append(container)
    return profiles


def _best_profile(container: dict[str, Any]) -> tuple[dict[str, Any] | None, float | None]:
    best_profile: dict[str, Any] | None = None
    best_lambda: float | None = None
    for profile in _candidate_profiles(container):
        lambda_min = _first_float(profile, BEST_LAMBDA_KEYS)
        if lambda_min is None:
            continue
        if best_lambda is None or lambda_min < best_lambda:
            best_lambda = lambda_min
            best_profile = profile
    return best_profile, best_lambda


def _coverage_status(container: dict[str, Any]) -> Any | None:
    for key in TRIAD_COVERAGE_KEYS:
        value = container.get(key)
        if value is not None:
            if isinstance(value, dict):
                for inner_key in ("status", "value", "mode"):
                    inner_value = value.get(inner_key)
                    if inner_value is not None:
                        return inner_value
            return value
    return None


def _coverage_ratio(container: dict[str, Any]) -> float | None:
    for key in ("triad_coverage_ratio", "coverage_ratio", "ratio"):
        value = _coerce_float(container.get(key))
        if value is not None:
            return value
    for key in TRIAD_COVERAGE_KEYS:
        value = container.get(key)
        if isinstance(value, dict):
            ratio = _first_float(value, ("triad_coverage_ratio", "coverage_ratio", "ratio"))
            if ratio is not None:
                return ratio
    return None


def _coverage_sample_count(container: dict[str, Any]) -> int | None:
    for key in ("triad_sample_count", "sample_count", "coverage_sample_count"):
        value = _coerce_int(container.get(key))
        if value is not None:
            return value
    for key in TRIAD_COVERAGE_KEYS:
        value = container.get(key)
        if isinstance(value, dict):
            sample_count = _first_int(value, ("triad_sample_count", "sample_count", "coverage_sample_count"))
            if sample_count is not None:
                return sample_count
    return None


def _coverage_sample_limit(container: dict[str, Any]) -> int | None:
    for key in ("triad_sample_limit", "sample_limit", "coverage_sample_limit"):
        value = _coerce_int(container.get(key))
        if value is not None:
            return value
    for key in TRIAD_COVERAGE_KEYS:
        value = container.get(key)
        if isinstance(value, dict):
            sample_limit = _first_int(value, ("triad_sample_limit", "sample_limit", "coverage_sample_limit"))
            if sample_limit is not None:
                return sample_limit
    return None


def _normalize_operator_sample_coverage_status(value: Any | None) -> str | None:
    if value is None:
        return None
    if isinstance(value, dict):
        for inner_key in ("status", "value", "mode"):
            inner_value = value.get(inner_key)
            if inner_value is not None:
                return _normalize_operator_sample_coverage_status(inner_value)
        return None
    text = str(value).strip().lower().replace("-", "_")
    if not text:
        return None
    if "sparse" in text or "limited" in text:
        return "sparse_sampled"
    if text in FULL_SAMPLE_COVERAGE_STATUSES or text.endswith("_full") or "full" in text:
        return "operator_full"
    if text in {"unknown", "unavailable", "mixed"}:
        return text
    return "unknown"


def _operator_sample_coverage_status(container: dict[str, Any]) -> str | None:
    return _normalize_operator_sample_coverage_status(_coverage_status(container))


def _degree_counter(container: dict[str, Any], keys: tuple[str, ...]) -> int | None:
    for key in keys:
        value = _coerce_int(container.get(key))
        if value is not None:
            return value
    for key in TRIAD_COVERAGE_KEYS:
        value = container.get(key)
        if isinstance(value, dict):
            counter = _first_int(value, keys)
            if counter is not None:
                return counter
    return None


def _coverage_counts_by_status(shells: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for shell in shells:
        status = shell.get("operator_sample_coverage_status")
        if not isinstance(status, str) or not status:
            continue
        counts[status] = counts.get(status, 0) + 1
    return counts


def _min_float(values: list[float | None]) -> float | None:
    filtered = [value for value in values if value is not None]
    if not filtered:
        return None
    return min(filtered)


def _merge_record(existing: dict[str, Any], incoming: dict[str, Any]) -> dict[str, Any]:
    merged = dict(existing)
    for key in ("best_lambda", "worst_eigen_shell", "worst_eigen_mass"):
        if merged.get(key) is None and incoming.get(key) is not None:
            merged[key] = incoming[key]
    if _coerce_float(incoming.get("best_lambda")) is not None:
        existing_lambda = _coerce_float(merged.get("best_lambda"))
        incoming_lambda = _coerce_float(incoming.get("best_lambda"))
        if existing_lambda is None or (
            incoming_lambda is not None and incoming_lambda < existing_lambda
        ):
            merged["best_lambda"] = incoming_lambda
            merged["worst_eigen_shell"] = incoming.get("worst_eigen_shell")
            merged["worst_eigen_mass"] = incoming.get("worst_eigen_mass")
    merged["tail_escape_candidate_count"] = int(merged.get("tail_escape_candidate_count", 0)) + int(
        incoming.get("tail_escape_candidate_count", 0) or 0
    )
    for key in ("triad_coverage_ratio", "operator_sample_coverage_ratio"):
        merged_value = _coerce_float(merged.get(key))
        incoming_value = _coerce_float(incoming.get(key))
        if merged_value is None:
            if incoming_value is not None:
                merged[key] = incoming_value
        elif incoming_value is not None:
            merged[key] = min(merged_value, incoming_value)

    merged_ok = merged.get("ok")
    incoming_ok = incoming.get("ok")
    if merged_ok is None:
        merged["ok"] = incoming_ok
    elif incoming_ok is not None:
        merged["ok"] = bool(merged_ok) and bool(incoming_ok)

    merged_checker_ok = merged.get("checker_ok")
    incoming_checker_ok = incoming.get("checker_ok")
    if merged_checker_ok is None:
        merged["checker_ok"] = incoming_checker_ok
    elif incoming_checker_ok is not None:
        merged["checker_ok"] = bool(merged_checker_ok) and bool(incoming_checker_ok)

    statuses = [
        status
        for status in (merged.get("triad_coverage_status"), incoming.get("triad_coverage_status"))
        if status is not None
    ]
    if not statuses:
        merged["triad_coverage_status"] = None
    else:
        unique = {json.dumps(status, sort_keys=True, default=str) for status in statuses}
        merged["triad_coverage_status"] = statuses[0] if len(unique) == 1 else "mixed"

    operator_statuses = [
        status
        for status in (
            merged.get("operator_sample_coverage_status"),
            incoming.get("operator_sample_coverage_status"),
        )
        if status is not None
    ]
    if not operator_statuses:
        merged["operator_sample_coverage_status"] = None
    else:
        unique = {json.dumps(status, sort_keys=True, default=str) for status in operator_statuses}
        merged["operator_sample_coverage_status"] = operator_statuses[0] if len(unique) == 1 else "mixed"

    for key in ("zero_degree_count", "empty_degree_count"):
        merged_value = _coerce_int(merged.get(key))
        incoming_value = _coerce_int(incoming.get(key))
        if merged_value is None:
            if incoming_value is not None:
                merged[key] = incoming_value
        elif incoming_value is not None:
            merged[key] = int(merged_value) + int(incoming_value)
    return merged


def _summarize_manifest(manifest: dict[str, Any], manifest_path: Path) -> list[dict[str, Any]]:
    runs = _manifest_runs(manifest)
    summaries: dict[int, dict[str, Any]] = {}
    for run in runs:
        shell = _coerce_int(run.get("shell"))
        if shell is None and isinstance(run.get("shell_dir"), str):
            try:
                shell = int(Path(run["shell_dir"]).name.split("_")[-1])
            except (TypeError, ValueError, IndexError):
                shell = None
        scan_payload = _scan_payload(run, manifest_path.parent)
        row = _select_row(scan_payload, shell) if scan_payload is not None else None
        if shell is None and isinstance(row, dict):
            shell = _coerce_int(row.get("shell"))
        if shell is None and isinstance(row, dict):
            shell = _coerce_int(row.get("snapshot_index"))
        source = row if isinstance(row, dict) else (scan_payload if isinstance(scan_payload, dict) else run)
        best_profile, best_lambda = _best_profile(source)
        profile_source = best_profile if isinstance(best_profile, dict) else source
        coverage_status = _coverage_status(source)
        operator_sample_coverage_status = _operator_sample_coverage_status(source)
        coverage_ratio = _coverage_ratio(source)
        coverage_sample_count = _coverage_sample_count(source)
        coverage_sample_limit = _coverage_sample_limit(source)
        zero_degree_count = _degree_counter(source, ZERO_DEGREE_COUNT_KEYS)
        empty_degree_count = _degree_counter(source, EMPTY_DEGREE_COUNT_KEYS)
        summary = {
            "shell": shell,
            "ok": run.get("ok"),
            "checker_ok": (
                run.get("checker").get("ok") if isinstance(run.get("checker"), dict) else None
            ),
            "best_lambda": best_lambda,
            "worst_eigen_shell": _first_int(profile_source, WORST_SHELL_KEYS),
            "worst_eigen_mass": _first_float(profile_source, WORST_MASS_KEYS),
            "tail_escape_candidate_count": _first_int(source, TAIL_ESCAPE_KEYS) or 0,
            "triad_coverage_status": coverage_status,
            "triad_coverage_ratio": coverage_ratio,
            "triad_sample_count": coverage_sample_count,
            "triad_sample_limit": coverage_sample_limit,
            "operator_sample_coverage_status": operator_sample_coverage_status,
            "operator_sample_coverage_ratio": coverage_ratio,
        }
        if zero_degree_count is not None:
            summary["zero_degree_count"] = zero_degree_count
        if empty_degree_count is not None:
            summary["empty_degree_count"] = empty_degree_count
        if shell is None:
            continue
        existing = summaries.get(shell)
        summaries[shell] = summary if existing is None else _merge_record(existing, summary)
    return [summaries[shell] for shell in sorted(summaries)]


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", dest="inputs", action="append", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    manifest_summaries: list[dict[str, Any]] = []
    for input_path in args.inputs:
        manifest = _read_json(input_path)
        manifest_summaries.extend(_summarize_manifest(manifest, input_path))

    merged: dict[int, dict[str, Any]] = {}
    for summary in manifest_summaries:
        shell = summary.get("shell")
        if not isinstance(shell, int):
            continue
        existing = merged.get(shell)
        merged[shell] = summary if existing is None else _merge_record(existing, summary)

    shells = [merged[shell] for shell in sorted(merged)]
    operator_sample_coverage_status_values = [
        shell.get("operator_sample_coverage_status")
        for shell in shells
        if shell.get("operator_sample_coverage_status") is not None
    ]
    operator_sample_coverage_ratio_min = _min_float(
        [
            _coerce_float(shell.get("operator_sample_coverage_ratio"))
            for shell in shells
        ]
    )
    triad_coverage_ratio_min = _min_float(
        [_coerce_float(shell.get("triad_coverage_ratio")) for shell in shells]
    )
    triad_coverage_values = [
        shell.get("triad_coverage_status")
        for shell in shells
        if shell.get("triad_coverage_status") is not None
    ]
    unique_coverage = {
        json.dumps(value, sort_keys=True, default=str) for value in triad_coverage_values
    }
    triad_coverage_status: Any | None
    if not triad_coverage_values:
        triad_coverage_status = None
    elif len(unique_coverage) == 1:
        triad_coverage_status = triad_coverage_values[0]
    else:
        triad_coverage_status = "mixed"
    operator_sample_coverage_counts = _coverage_counts_by_status(shells)

    zero_degree_count_values = [
        _coerce_int(shell.get("zero_degree_count")) for shell in shells if shell.get("zero_degree_count") is not None
    ]
    empty_degree_count_values = [
        _coerce_int(shell.get("empty_degree_count")) for shell in shells if shell.get("empty_degree_count") is not None
    ]

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "candidate_only": True,
        "manifest_count": len(args.inputs),
        "shell_count": len(shells),
        "ok_count": sum(1 for shell in shells if shell.get("ok") is True),
        "checker_ok_count": sum(1 for shell in shells if shell.get("checker_ok") is True),
        "tail_escape_candidate_count": sum(
            int(shell.get("tail_escape_candidate_count", 0) or 0) for shell in shells
        ),
        "triad_coverage_status": triad_coverage_status,
        "triad_coverage_ratio_min": triad_coverage_ratio_min,
        "operator_sample_coverage_status": (
            None
            if not operator_sample_coverage_status_values
            else (
                operator_sample_coverage_status_values[0]
                if len({
                    json.dumps(value, sort_keys=True, default=str)
                    for value in operator_sample_coverage_status_values
                })
                == 1
                else "mixed"
            )
        ),
        "operator_sample_coverage_status_counts": operator_sample_coverage_counts,
        "operator_sample_coverage_ratio_min": operator_sample_coverage_ratio_min,
        "shells": shells,
    }
    if zero_degree_count_values:
        payload["zero_degree_count"] = sum(int(value or 0) for value in zero_degree_count_values)
    if empty_degree_count_values:
        payload["empty_degree_count"] = sum(int(value or 0) for value in empty_degree_count_values)

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload) + "\n", encoding="utf-8")
    print(_json_text(payload))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
